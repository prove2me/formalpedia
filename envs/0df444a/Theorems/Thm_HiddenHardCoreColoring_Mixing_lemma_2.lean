-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_2
-- name    : HiddenHardCoreColoring.Mixing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:11.220196+00:00
-- url     : https://prove2.me/theorems/6038a1cf-6056-4ef2-bcee-41856b105672
-- title:
--   Lemma 2 — mixing time at most gap(P)⁻¹ log(1/(ε µ_min)) for an irreducible positive chain
-- statement:
--   Let $P$ be a transition matrix on a finite nonempty state space $\Omega$, reversible with respect to a probability distribution $\mu$ with $\mu(\sigma)>0$ for every $\sigma$, and let $\mu_{\min}=\min_\sigma\mu(\sigma)$. If $P$ is irreducible and has no negative eigenvalues, then for every $\varepsilon\in(0,1)$ some time succeeds and
--   $$t_{\mathrm{mix}}(P,\varepsilon)\le\frac1{\operatorname{gap}(P)}\log\frac1{\varepsilon\,\mu_{\min}} .$$
--
--   This is the standard conversion of a spectral gap into a mixing-time bound, stated without rounding loss; Theorem 1 applies it to the coloring chain, which is positive semidefinite.
--
--   Differences from the source:
--   - encoding: t_mix(P, ε) ≤ B, with t_mix the minimum successful time → some time t succeeds (max_σ d_TV(P^t(σ,·), µ) ≤ ε) and the natural-number infimum tmix of the successful times is ≤ B; reason: the minimum exists exactly when a successful time exists; the conjunction never uses Lean's value sInf ∅ = 0
--   - encoding: eigenvalues of the reversible chain listed with multiplicity, gap(P) = 1 − λ₂(P) → gap P = 1 − λ₂ with λ₂ := 1 if the eigenspace of 1 has dimension ≥ 2 and otherwise the largest real eigenvalue ≠ 1; reason: for a chain reversible with respect to a full-support law all eigenvalues are real and at most 1, so this is the second eigenvalue counted with multiplicity
--   - generalization: gap(P) = 1 − λ₂(P), with λ₂ defined by the eigenvalue list (so requiring at least two states) → the same bound also holds on a singleton state space, with gap(P) = 1; reason: on two or more states the gap is exactly the source gap; on a singleton P = [1], µ_min = 1 and t_mix = 0, so the extension holds for every ε ∈ (0,1)
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 2, eq. (1), p.6; standing assumptions of §3.1, p.6

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Chain

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 2** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.6). Let `P` be a finite chain reversible with respect to a
full-support law `µ`, and `µ_min := min_σ µ(σ)`. If `P` is irreducible and has no negative eigenvalues,
then for every `ε ∈ (0, 1)`, `t_mix(P, ε) ≤ gap(P)⁻¹ log(1/(ε µ_min))`; a successful time exists. -/
theorem lemma_2 {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] (P : Matrix S S ℝ) (μ : S → ℝ)
    (hrev : IsReversibleFullSupport P μ) (hirr : MarkovMixing.Irreducible P)
    (hnn : ∀ lam : ℝ, MarkovMixing.IsEigenvalue P lam → 0 ≤ lam) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∃ t : ℕ, MixedAt P μ ε t) ∧
      (tmix P μ ε : ℝ) ≤ 1 / gap P * Real.log (1 / (ε * muMin μ)) := by sorry

end HiddenHardCoreColoring.Mixing
