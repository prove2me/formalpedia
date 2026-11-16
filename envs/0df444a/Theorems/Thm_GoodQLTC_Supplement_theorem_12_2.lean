-- Prove2me | Theorems.Thm_GoodQLTC_Supplement_theorem_12_2
-- name    : GoodQLTC.Supplement.theorem_12_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:01:37.336662+00:00
-- url     : https://prove2.me/theorems/1c28e9e6-5f20-4e82-9b68-d946739ebb57
-- title:
--   Theorem 12.2 — interior interpolation on unequal norm-one grids
-- statement:
--   Let $k$ be an algebraically closed field of characteristic two, $t\ge4$ an integer and $\tau\ge1$ a real number. For $1\le r\le t$ let $2\le q_1<\dots<q_r$ be powers of two with $q_r\le\tau q_1$, put $\Omega_i:=\{z\in k:z^{q_i+1}=1\}$, $n_i:=q_i+1$, $\Omega:=\prod_{i=1}^r\Omega_i$, and fix an integer $0\le\ell<n_1$. Write $k[X]_{\le h}$ for the polynomials in $X=(X_1,\dots,X_r)$ of total degree at most $h$.
--
--   There is an integer $C=C(t,\tau)\ge1$ such that, for every choice of $r$, $\{q_i\}$, $\ell$ as above and every $\ell$-closed set $T\subseteq\Omega$, the evaluation map
--   $$k[X]_{\le C\ell}\longrightarrow k^{T^\circ},\qquad P\longmapsto P|_{T^\circ},$$
--   is surjective. Here $\ell$-closed sets and the interior $T^\circ$ are those of Definition 12.1.
--
--   This interpolation bound is what makes the product-expansion constant of Reed–Solomon codes on norm-one grids (Theorem 13.1) uniform in $r$ and the field sizes.
--
--   **Formalization Note** The constant is the explicit integer `GoodQLTC.rsConstC t τ` of the published `GoodQLTC.rsRho` (p.46: $m:=t-2$, $c:=t2^t$, $a:=\lceil t\tau\rceil$, $p_0:=0$, $p_d:=dp_{d-1}+1$, $B:=2ta+4c\sum_{d=1}^m d!(2a)^dt^{d-1}$, $C:=taB^{p_m}$), chosen before $k$, $r$, $\{q_i\}$, $\ell$, $T$. Surjectivity is stated as: every function $T^\circ\to k$ is $P|_{T^\circ}$ for some $P$ of total degree at most $C\ell$.
--
--   Differences from the source:
--   - generalization: there is an integer C = C(t, τ) ≥ 1 → C := rsConstC t τ, the integer C := taB^{p_m} fixed in the proof (p.46), with 1 ≤ C; reason: the explicit constant specializes to the printed existential; it is the same C that enters ρ of (13.1)
--   - encoding: q_r ≤ τ q_1 and 0 ≤ ℓ < n_1 → q_i ≤ τ q_j for all i, j and ℓ < q_i + 1 for all i; reason: equivalent because q_1 < ⋯ < q_r
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 12.2, p.40 (PDF 43), with the standing data of §12, p.39 (PDF 42) and the constant C of the proof, p.46 (PDF 49)

import Mathlib
import Definitions.Def_GoodQLTC_rsRho
import Definitions.Def_GoodQLTC_Supplement_gridInterior

namespace GoodQLTC.Supplement

open GoodQLTC

/-- **Theorem 12.2** (interior interpolation on norm-one grids), Gay–Jeronimo, arXiv:2609.20780
(held version), p.40, with the standing data of §12, p.39: `k` algebraically closed of
characteristic two, an integer `t ≥ 4` and a real `τ ≥ 1`. There is an integer `C = C(t, τ) ≥ 1`
such that, for every `1 ≤ r ≤ t`, all powers of two `2 ≤ q_1 < ⋯ < q_r` with `q_r ≤ τ q_1`, every
integer `0 ≤ ℓ < n_1 = q_1 + 1`, and every `ℓ`-closed `T ⊆ Ω`, the evaluation map
`k[X]_{≤Cℓ} → k^{T°}`, `P ↦ P|_{T°}`, is surjective.

**Formalization Note.** `C` is the explicit integer `rsConstC t τ` fixed in the proof (p.46:
`C := t a B^{p_m}`), the same constant that enters `ρ` of (13.1); the statement asserts `1 ≤ C` and
the interpolation property for it, which implies the printed `∃ C`. `C` is chosen before `k`, `r`,
`{q_i}`, `ℓ` and `T`. `k[X]_{≤h}` is total degree `≤ h` (`MvPolynomial.totalDegree`); `P_ℓ` in the
closure is degree `≤ ℓ` in each variable. `q_r ≤ τ q_1` is written `q_i ≤ τ q_j` for all `i, j`
and `ℓ < n_1` as `ℓ < q_i + 1` for all `i` (equivalent, `q` increasing). Surjectivity onto `k^{T°}`:
every function `T° → k` is the restriction of such a `P`. -/
theorem theorem_12_2 (t : ℕ) (τ : ℝ) (ht : 4 ≤ t) (hτ : 1 ≤ τ) :
    1 ≤ rsConstC t τ ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k 2] (r : ℕ), 1 ≤ r → r ≤ t →
      ∀ q : Fin r → ℕ, (∀ i, ∃ e : ℕ, q i = 2 ^ e) → (∀ i, 2 ≤ q i) → StrictMono q →
        (∀ i j, (q i : ℝ) ≤ τ * (q j : ℝ)) →
      ∀ ℓ : ℕ, (∀ i, ℓ < q i + 1) →
      ∀ T : Set (Fin r → k), T ⊆ normOneGrid q → IsGridClosed q ℓ T →
      ∀ y : gridInterior q T → k, ∃ P : MvPolynomial (Fin r) k,
        P.totalDegree ≤ rsConstC t τ * ℓ ∧ ∀ z : gridInterior q T, MvPolynomial.eval z.1 P = y z := by sorry

end GoodQLTC.Supplement
