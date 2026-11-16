-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_4_5
-- name    : GoldProxGap.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:46:49.886774+00:00
-- url     : https://prove2.me/theorems/4cdeec38-1e05-455c-9c5a-2ba9c6199dde
-- title:
--   Theorem 4.5 — every fixed rate on every additive domain: $\Omega_{\rho,s}(N^s)$ exceptional challenges at agreement $\lceil\alpha N\rceil$, $\rho<\alpha<\sqrt\rho$
-- statement:
--   **Theorem 4.5 (Every fixed rate on every additive domain).** Fix $0<\rho<1$ and an integer $s\ge2$. There are constants $\alpha$ and $c>0$, depending only on $\rho$ and $s$, with $\rho<\alpha<\sqrt\rho$, such that the following hold for every sufficiently large binary additive domain $D$ of size $N$ in a finite field $\mathbb F$ of characteristic two and size $q$, with
--
--   $$
--   K=\lfloor\rho N\rfloor,\qquad T=\lceil\alpha N\rceil .
--   $$
--
--   1. There is a pair with $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$ and
--   $$
--   \frac{|\mathrm{Bad}_T(f,g)\setminus\{0\}|}{q}\ \ge\ \frac{1}{1+q/(cN^s)}-\frac1q, \tag{4.5}
--   $$
--   so that $|\mathrm{Bad}_T(f,g)\setminus\{0\}|\ge\tfrac12\min\{q,cN^s\}-1$.
--   2. If $q\le N^a$ for a fixed $a\ge1$ with $s>2a$, there is a pair with $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$ and $\mathrm{Bad}_T(f,g)=\mathbb F$ (zero included).
--   3. If $D\subseteq\mathbb B\subsetneq\mathbb F$ for a subfield $\mathbb B$, there is a pair with $\mathrm{agr}_K(f)=\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$ and
--   $$
--   |\mathrm{Bad}_T(f,g)\setminus\{0\}|\ \ge\ \frac{|\mathbb B|}{1+|\mathbb B|/(cN^s)}-1 ;
--   $$
--   if moreover $[\mathbb F:\mathbb B]\ge s+1$, there is a pair with these three agreements equal to $K$ that satisfies (4.5).
--
--   For the pairs of parts 1 and 2, the first input $f$ has at least as many codewords of message length $K+1$ at agreement $T$ as the pair has exceptional challenges: $|\mathrm{Bad}_T(f,g)|\le|L_T(f)|$ for the code of message length $K+1$.
--
--   The theorem shows that at every fixed rate the agreement $\alpha N$ with $\alpha<\sqrt\rho$ (below the Johnson bound) admits a polynomial number of exceptional challenges of arbitrarily large degree $s$, on every binary additive domain.
--
--   **Formalization Note** "Sufficiently large" is an explicit threshold $N_0$ on $N=|D|$: one $N_0$, independent of $\mathbb F$ and $q$, for parts 1 and 3, and for each fixed $a$ one $N_0$ for part 2. $D$ is an additive subgroup of $\mathbb F$; $\mathbb B$ ranges over the proper subfields of $\mathbb F$ containing $D$, and $[\mathbb F:\mathbb B]$ is `Module.finrank`. $N^s$ is a natural power and $N^a$ a real power.
--
--   Differences from the source:
--   - reading: for every sufficiently large binary additive domain D of size N in a finite field F of size q → ∃ N₀ (after α, c; independent of F and q) for parts 1 and 3, and for every a ≥ 1 with s > 2a an ∃ N₀ for part 2; the conclusion holds whenever N ≥ N₀; reason: the explicit form of 'sufficiently large'; in part 2 the threshold may depend on the fixed a, as in the proof (cN^s > (q − 1)² needs N large in terms of a)
--   - encoding: binary additive domain D in F → D₀ : AddSubgroup F, F a finite field with CharP F 2, N = Nat.card D₀; reason: in characteristic two the additive subgroups are exactly the F₂-subspaces
--   - encoding: Equivalently, at least q/(1 + q/(cN^s)) − 1 ≥ (1/2) min{q, cN^s} − 1 distinct nonzero exceptional challenges; in particular Ω_{ρ,s}(N^s) when q ≥ N^s → (4.5) and the count |Bad_T \ {0}| ≥ (1/2) min{q, cN^s} − 1; reason: the middle expression is (4.5) multiplied by q, and the Ω remark follows from the count form with q ≥ N^s
--   - encoding: Bad_T(f, g) = F; here zero is exceptional as well → Bad_T(f, g) = Finset.univ; reason: zero belongs to Finset.univ
--   - encoding: D ⊆ B ⊊ F → B : Subfield F with D₀ ≤ B and B ≠ ⊤; |B| = Nat.card B, [F : B] = Module.finrank B F; reason: a proper subfield of the challenge field containing the domain
--   - reading: For the pairs of the first two parts, the first input f also has at least as many codewords of the code of message length K + 1 at agreement T as the pair has exceptional challenges → (Bad_T(f, g)).card ≤ (decodingList D (K + 1) T f).card for the pairs of parts 1 and 2; reason: the sentence follows the three items inside the theorem environment; the stronger reading (it is part of the theorem) is kept
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 4.5, pp.31–32

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 4.5 (Every fixed rate on every additive domain)**, pp.31–32. Dao, Kominers,
Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Fix 0 < ρ < 1 and an integer s ≥ 2. There are constants α and c > 0, depending only on ρ and s,
with ρ < α < √ρ, such that the following hold for every sufficiently large binary additive domain
D of size N in a finite field F of size q, with K = ⌊ρN⌋, T = ⌈αN⌉.
1. There is a pair with agr_K(g) = CA_K(f, g) = K and
|Bad_T(f, g) \ {0}|/q ≥ 1/(1 + q/(cN^s)) − 1/q. (4.5)
Equivalently, there are at least q/(1 + q/(cN^s)) − 1 ≥ (1/2) min{q, cN^s} − 1 distinct nonzero
exceptional challenges; in particular, q ≥ N^s gives Ω_{ρ,s}(N^s) of them.
2. If q ≤ N^a for a fixed a ≥ 1 with s > 2a, there is a pair with agr_K(g) = CA_K(f, g) = K and
Bad_T(f, g) = F. Here zero is exceptional as well.
3. If D ⊆ B ⊊ F, there is a pair with agr_K(f) = agr_K(g) = CA_K(f, g) = K,
|Bad_T(f, g) \ {0}| ≥ |B|/(1 + |B|/(cN^s)) − 1. If moreover [F : B] ≥ s + 1, there is a pair with
these three agreements equal to K that satisfies (4.5).
For the pairs of the first two parts, the first input f also has at least as many codewords of
the code of message length K + 1 at agreement T as the pair has exceptional challenges."

**Formalization Note.**
* `α`, `c` are chosen after `ρ`, `s` and before everything else. "Every sufficiently large
  binary additive domain" is an explicit threshold `N₀` on `N = |D|`: one `N₀` (depending on
  `ρ, s, α, c` only, never on `F` or `q`) for parts 1 and 3, and for part 2 one `N₀` for each
  fixed `a` ("a fixed a ≥ 1").
* A binary additive domain of size `N` in `F` is an additive subgroup `D₀ : AddSubgroup F` of a
  finite field of characteristic two with `Nat.card D₀ = N`; `K = ⌊ρN⌋₊`, `T = ⌈αN⌉₊`.
* `N^s` is a natural power of the real `N`; `N^a` is `Real.rpow`. `Bad_T(f, g) \ {0}` is
  `(Bad …).erase 0`.
* Part 1 states (4.5) and the count form `|Bad_T \ {0}| ≥ (1/2) min{q, cN^s} − 1`; the middle
  expression `q/(1 + q/(cN^s)) − 1` is (4.5) multiplied by `q`, and the `Ω` remark follows from
  the count form.
* Part 3: `B` ranges over the proper subfields of `F` containing `D` (`B : Subfield F`,
  `D₀ ≤ B`, `B ≠ ⊤`), `|B| = Nat.card B`, `[F : B] = Module.finrank B F`; the pair for
  `[F : B] ≥ s + 1` may differ from the first pair of part 3.
* The final sentence is part of the theorem: for the pairs of parts 1 and 2,
  `|Bad_T(f, g)| ≤ |decodingList D (K + 1) T f|` (all exceptional challenges, zero included). -/
theorem theorem_4_5 (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (s : ℕ) (hs : 2 ≤ s) :
    ∃ α c : ℝ, ρ < α ∧ α < Real.sqrt ρ ∧ 0 < c ∧
      (∃ N₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (D₀ : AddSubgroup F),
        N₀ ≤ Nat.card D₀ →
        let N : ℕ := Nat.card D₀
        let q : ℝ := Fintype.card F
        let K : ℕ := ⌊ρ * N⌋₊
        let T : ℕ := ⌈α * N⌉₊
        let Dom : Finset F := domainFinset D₀
        -- Part 1
        (∃ f g : Dom → F,
          agr Dom K g = K ∧ CA Dom K f g = K ∧
          1 / (1 + q / (c * (N : ℝ) ^ s)) - 1 / q ≤ (((Bad Dom K T f g).erase 0).card : ℝ) / q ∧
          (1 / 2 : ℝ) * min q (c * (N : ℝ) ^ s) - 1 ≤ (((Bad Dom K T f g).erase 0).card : ℝ) ∧
          (Bad Dom K T f g).card ≤ (decodingList Dom (K + 1) T f).card) ∧
        -- Part 3
        (∀ B : Subfield F, D₀ ≤ B.toAddSubgroup → B ≠ ⊤ →
          (∃ f g : Dom → F,
            agr Dom K f = K ∧ agr Dom K g = K ∧ CA Dom K f g = K ∧
            (Nat.card B : ℝ) / (1 + (Nat.card B : ℝ) / (c * (N : ℝ) ^ s)) - 1 ≤
              (((Bad Dom K T f g).erase 0).card : ℝ)) ∧
          (s + 1 ≤ Module.finrank B F →
            ∃ f g : Dom → F,
              agr Dom K f = K ∧ agr Dom K g = K ∧ CA Dom K f g = K ∧
              1 / (1 + q / (c * (N : ℝ) ^ s)) - 1 / q ≤
                (((Bad Dom K T f g).erase 0).card : ℝ) / q))) ∧
      -- Part 2
      (∀ a : ℝ, 1 ≤ a → 2 * a < s →
        ∃ N₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (D₀ : AddSubgroup F),
          N₀ ≤ Nat.card D₀ →
          let N : ℕ := Nat.card D₀
          let q : ℝ := Fintype.card F
          let K : ℕ := ⌊ρ * N⌋₊
          let T : ℕ := ⌈α * N⌉₊
          let Dom : Finset F := domainFinset D₀
          q ≤ (N : ℝ) ^ a →
          ∃ f g : Dom → F,
            agr Dom K g = K ∧ CA Dom K f g = K ∧ Bad Dom K T f g = Finset.univ ∧
            (Bad Dom K T f g).card ≤ (decodingList Dom (K + 1) T f).card) := by sorry

end GoldProxGap.Supplement
