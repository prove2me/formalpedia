-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_6_7
-- name    : LIPAlgorithm.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:46.144931+00:00
-- url     : https://prove2.me/theorems/54491ecd-9bab-4719-8d11-ea89a59dd49c
-- title:
--   Lemma 6.7 — collision scale
-- statement:
--   Let $\mu=D_{L^*,s}$ and $S_2(\mu)=(\sum_{x\in L^*}\mu(x)^2)^{-1}$.
--
--   1. For every full-rank lattice $L$ of rank $n\ge1$ and every $s>0$,
--   $$S_2(D_{L^*,s})=\frac{\rho_s(L^*)^2}{\rho_{s/\sqrt2}(L^*)}.$$
--   2. For every $C>0$, $\delta>0$ there is $n_0$ such that for $n\ge n_0$, $L$ rank-$n$ well-rounded and $s=Cn^2\log n/\lambda_1(L)$,
--   $$\Big|\frac{S_2(D_{L^*,s})}{2^{n/2}s^n/\det L^*}-1\Big|\le\delta.$$
--   3. For every $C>0$ there are $C'$ and $n_0$ such that for such $n$ and $L$, $S_2(D_{L^*,s})\le(C'n^2\log n)^n$.
--
--   This sets the number of samples of the birthday algorithm, and so its running time.
--
--   Differences from the source:
--   - generalization: the identity for s = Cn²log n/λ, L well-rounded → for every s > 0 and every lattice; reason: the identity is algebraic; the source's case is an instance
--   - generalization: 'for C sufficiently large' → every C > 0, with n₀ after C; reason: large n absorbs small C; the source's range is a sub-range
--   - encoding: (1 ± o(1)) → ∀δ > 0, ∃n₀, uniformly in L; reason: the meaning of o(1) with respect to n, p.8
--   - reading: 'computable from the input' → the closed formula 2^{n/2}sⁿ/det L* in clause 2; reason: the sentence is a remark on that formula, with no model or time named; running costs are carried by theorem_7_1
--   - encoding: det L* → ZLattice.covolume (dual L); reason: the volume of a fundamental domain is √det(B⊤B), p.9
--   - reading: log n with no named base → Real.logb 2; reason: a change of base only rescales C in s; base 2 gives the smaller threshold r*(n)
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 6.7, p.34

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Lemma 6.7 (Collision scale).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 6.7, p.34
(PDF p.37), for `s = C·n²·log n/λ`.

(i) `S₂(D_{L*,s}) = ρ_s(L*)²/ρ_{s/√2}(L*)`. (ii) `S₂ = (1 ± o(1))·2^{n/2}·sⁿ/det L*`, uniformly in `L`. (iii) `S₂ ≤ (C'·n²·log n)ⁿ`, with `C'`
depending on `C`.

**Formalization Note.** (i) is stated for every `s > 0`, since it is an identity; (ii), (iii) for every `C > 0` with `n₀` after `C`, which covers
the printed "for C sufficiently large". `det L*` is `ZLattice.covolume`. The printed "computable from the input" is the closed formula in (ii). -/
theorem lemma_6_7 :
    (∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℝ), 1 ≤ n → 0 < s →
      collisionScale L s =
        RegevLWE.Hyperplane.rhoDual s L ^ 2 / RegevLWE.Hyperplane.rhoDual (s / Real.sqrt 2) L) ∧
    ∀ C : ℝ, 0 < C →
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
        ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L],
          n₀ ≤ n → IsWellRounded L →
            |collisionScale L (scaleS C L) /
                ((2 : ℝ) ^ ((n : ℝ) / 2) * scaleS C L ^ n /
                  ZLattice.covolume (RegevLWE.GaussConv.dual L)) - 1| ≤ δ) ∧
      ∃ (C' : ℝ) (n₀ : ℕ),
        ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L],
          n₀ ≤ n → IsWellRounded L →
            collisionScale L (scaleS C L) ≤ (C' * (n : ℝ) ^ 2 * Real.logb 2 n) ^ n := by sorry

end LIPAlgorithm
