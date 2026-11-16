-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_8_6
-- name    : LinSysAmp.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:54:02.866596+00:00
-- url     : https://prove2.me/theorems/1b6e907e-cd76-42ee-b09b-06fa40281237
-- title:
--   Theorem 8.6 — key recovery from a distinguisher for the extracted key bit
-- statement:
--   Let $q=2^\ell$, fix an $\mathbb F_2$-linear bijection $\mathrm{enc}:\mathbb F_q\to\{0,1\}^\ell$, and let $n\ge1$. Let $D$ be an algorithm, taking time $T$ per call, which distinguishes $(\tau,s,\langle s,\mathrm{enc}(K)\rangle)$ from $(\tau,s,u)$ with advantage $\varepsilon$ on the ideal distribution of the protocol: $\tau=(M,r,y)$ with $M\leftarrow GL_n(\mathbb F_q)$, $r,y$ uniform, $K=rM^{-1}y$, $s\leftarrow\{0,1\}^\ell\setminus\{0\}$ and $u\leftarrow\{0,1\}$. Then there is an algorithm which runs in time
--   $$\mathrm{poly}(\ell,1/\varepsilon)\cdot(T+n^2)$$
--   and recovers $K$ from $\tau$ with probability at least $\varepsilon^3/128$ on the ideal distribution.
--
--   So a distinguisher for one Goldreich–Levin bit of the key gives a key-recovery attack, which links bit security of the protocol to key-recovery security.
--
--   **Formalization Note** The algorithm is a program of the oracle machine with the distinguisher interface, chosen after the field and enc and before $n$, $\varepsilon$ and $D$. The polynomial is $C(\ell/\varepsilon)^d$ with $C,d$ absolute.
--
--   Differences from the source:
--   - reading: "distinguishes … with advantage ε" → ε ≤ |Pr[D(τ, s, ⟨s, enc K⟩) = 1] − Pr[D(τ, s, u) = 1]|; reason: Definition 8.1 bounds the absolute value, and the proof handles a negative advantage with 1 − D
--   - encoding: time poly(ℓ, 1/ε)·(T + n²) → on every run: calls ≤ C(ℓ/ε)^d and operations ≤ C(ℓ/ε)^d·n², with C, d absolute; reason: for ℓ ≥ 1 and ε ≤ 1, C(ℓ/ε)^d dominates every polynomial in ℓ and 1/ε of degree at most d; T is charged per call
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed advantage ε → they hold for every oracle; only the success guarantee assumes the advantage ε; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: ε unconstrained above → ε ≤ 1 added; reason: an advantage is at most 1, so the hypothesis forces it; without it (ℓ/ε)^d could be made arbitrarily small
--   - encoding: enc : F_q → {0,1}^ℓ an F₂-linear bijection; bits → an additive equivalence F ≃+ (Fin ℓ → ZMod 2); bits passed to D as field cells 0 / 1; reason: every additive map between F₂-vector spaces is F₂-linear
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 8.6, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_LinSysAmp_lineqSuccess
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_KeyAgreement

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 8.6 (Key recovery from a distinguisher), p.49 (PDF p.51). Couteau, Melissaris,
Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography*,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let q = 2^ℓ, and let D be a time-T algorithm which distinguishes (τ, s, ⟨s, enc(K)⟩) from
(τ, s, u) with advantage ε, on the ideal distribution of the protocol. Then there is an algorithm
which runs in time poly(ℓ, 1/ε) · (T + n²) and recovers K with probability at least ε³/128."

**Formalization Note.**
* *Setting.* `F` is any finite field with `2^ℓ` elements and `enc : F ≃+ {0,1}^ℓ` any fixed
  `F₂`-linear bijection (§8.1, p.47), both fixed before the algorithm. The ideal distribution is
  `M ← GL_n(F)`, `r, y ← Fⁿ` independent, `K = rM⁻¹y`, with the seed `s ← {0,1}^ℓ \ {0}`.
* *Advantage.* "Distinguishes with advantage ε" is `ε ≤ |distAdvantage enc D|` (Definition 8.1 uses
  the absolute value; the proof handles a negative advantage with `1 − D`), `ε > 0`.
* *Algorithm.* A program of `LinSysAmp.Supplement.OracleMachine` with the interface `distIface D`
  (a call passes `(M, r, y, s, b)` to `D`, the bits as field elements `0`/`1`). Input: the
  transcript `M` (row-major), `r`, `y`; index registers `par n ε`. Program and `par` are chosen
  after the field and `enc`, before `n`, `ε` and `D`. Output: the one-element list `[K]`.
* *Time* `poly(ℓ, 1/ε)·(T + n²)`: there are constants `C, d`, uniform over `ℓ`, the field, `enc`,
  `n`, `ε` and `D`, such that every run on every transcript makes at most `C(ℓ/ε)^d` calls and
  `C(ℓ/ε)^d n²` field operations (`ℓ ≥ 1` and `ε ≤ 1`, so `(ℓ/ε)^d` dominates every polynomial of
  degree `≤ d` in `ℓ` and `1/ε` up to a constant).
* *Success.* `E_{M,r,y}[Pr[output = rM⁻¹y]] ≥ ε³/128` on the ideal distribution.
* `n ≥ 1` (§3.1).
* `ε ≤ 1` is added: an advantage is at most `1`, so the hypothesis already forces it; the cost
  clause holds for every distinguisher, and without it `(ℓ/ε)^d` could be made arbitrarily small. -/
theorem theorem_8_6 :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧
      ∀ (ℓ : ℕ) (F : Type u) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = 2 ^ ℓ →
      ∀ enc : F ≃+ (Fin ℓ → ZMod 2),
      ∃ P : OProgram F, ∃ par : ℕ → ℝ → List ℤ,
        ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ D : Distinguisher n ℓ F,
          let Bc : ℝ := C * ((ℓ : ℝ) / ε) ^ d
          let Bo : ℝ := C * ((ℓ : ℝ) / ε) ^ d * (n : ℝ) ^ 2
          let N : ℕ := stepBudget Bc Bo
          (∀ (M : Matrix (Fin n) (Fin n) F) (r y : Fin n → F),
            OHaltsWithin (distIface D) P
              (oinit (par n ε) (flatMat M ++ List.ofFn r ++ List.ofFn y)) N Bc Bo) ∧
          (ε ≤ |distAdvantage enc D| →
            ε ^ 3 / 128 ≤
              ((Fintype.card (LinSysAmp.InvMat n F) : ℝ) * (Fintype.card F : ℝ) ^ n *
                  (Fintype.card F : ℝ) ^ n)⁻¹ *
                ∑ M : LinSysAmp.InvMat n F, ∑ r : Fin n → F, ∑ y : Fin n → F,
                  oOutputProb (distIface D) P
                    (oinit (par n ε) (flatMat M.1 ++ List.ofFn r ++ List.ofFn y)) N
                    (.vec [idealKey M.1 r y])) := by sorry

end LinSysAmp.Supplement
