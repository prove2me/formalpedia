-- Prove2me | Theorems.Thm_InfoInundation_CompleteScreening_proposition_1_all_accuracy_cases
-- name    : InfoInundation.CompleteScreening.proposition_1_all_accuracy_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:03.779252+00:00
-- url     : https://prove2.me/theorems/3a3060a2-f237-40fd-9e0c-2dbb15254db4
-- title:
--   Proposition 1(a) and (b) — closest-post optimality with both ex-post accuracy cases
-- statement:
--   Let $G$ be any Borel probability law for a positive noise standard deviation $\Sigma$, carried by some $[\mathrm{lo},\mathrm{hi}]$ with $0<\mathrm{lo}\le\mathrm{hi}<\infty$. No density or finite-support assumption is imposed. Let $\mu\in\mathbb R$, $s>0$, and let $Z_i\in\mathbb R$ be a menu indexed by $i\in I_K=\{0,\ldots,K-1\}$, for any natural number $K$. Write
--
--   $$
--   C(\mu,Z)=\{i\in I_K:\ \forall j\in I_K,\ (Z_i-\mu)^2\le(Z_j-\mu)^2\}.
--   $$
--
--   The consumer's normal belief is $N(\mu,s^2)$. Updating with estimated scale $a$ gives $s'(s,a)=\sqrt{s^2a^2/(s^2+a^2)}$. Under ex-post known accuracy, define
--
--   $$
--   S_{\mathrm{known,sd}}(z)=s-\mathbb E_G[s'(s,\Sigma)\mid z;\mu,s],\qquad
--   S_{\mathrm{known,var}}(z)=s^2-\mathbb E_G[s'(s,\Sigma)^2\mid z;\mu,s],
--   $$
--
--   where the conditional expectation is the Bayes ratio (4) with the predictive normal likelihood (5), of variance $s^2+\Sigma^2$. Under ex-post unknown accuracy, equation (2) instead uses
--
--   $$
--   A(\mu,s,z)=\int(u-z)^2\,dN(\mu,s^2)(u),\quad
--   S_{\mathrm{unknown,sd}}(z)=s-s'(s,\sqrt A),\quad
--   S_{\mathrm{unknown,var}}(z)=s^2-s'(s,\sqrt A)^2.
--   $$
--
--   Here $A=A(\mu,s,z)$ is evaluated under the current unconditioned belief, rather than a posterior conditional on $z$.
--
--   1. If $G\ne\delta_\sigma$ for every real $\sigma$, then the entire set of maximizing indices of each of the four scores equals the closest-post set:
--
--   $$
--   \operatorname*{argmax}_{i\in I_K}S(Z_i)=C(\mu,Z)
--   \quad\text{for }S\in\{S_{\mathrm{known,sd}},S_{\mathrm{known,var}},S_{\mathrm{unknown,sd}},S_{\mathrm{unknown,var}}\}.
--   $$
--
--   2. If $G=\delta_\sigma$ for some $\sigma>0$ and the scale is known, then both known-accuracy scores maximize over the entire menu:
--
--   $$
--   \operatorname*{argmax}_{i\in I_K} S_{\mathrm{known,sd}}(Z_i)
--   =\operatorname*{argmax}_{i\in I_K} S_{\mathrm{known,var}}(Z_i)=I_K.
--   $$
--
--   This is all of Proposition 1(a) and (b), including the two ex-post estimation cases explicitly included in the paragraph preceding the proposition. Equal-distance posts and repeated values remain separate maximizing choices. The proved reference `InfoInundation.Screening.proposition_1` supplies the known-accuracy clauses; this complete goal additionally exposes the missing equation (2) clauses. In the deterministic-known benchmark the actual known scale is used, as in the source.
--
--   **Formalization Note** The assumptions are exactly the positive bounded support convention and positive current standard deviation. The Gaussian moment identity and the positivity of all denominators must be proved, not assumed. The published derivative reference corrects a factor ½ in the proof; no correction of the goal is needed.
--
--   Differences from the source:
--   - reading: the displayed Screening Equation subtracts standard deviations but the prose calls the objective a variance decrease → the complete conclusion holds for both the sd and variance scores in both ex-post regimes; reason: this asserts both readings of the ambiguity without identifying their numerical scores
--   - generalization: each consumer and time has a reachable normal belief with initial standard deviation one → every real mean μ and every standard deviation s>0; reason: all source states are included; positivity is preserved by the source update and no reachability restriction is needed for the one-step comparison
--   - generalization: the operational menu has K≥1 posts → all K∈ℕ including K=0; reason: the empty menu makes all optimization sets empty and includes every nonempty source menu
--   - encoding: posts in a finite menu, with support of G containing at least two distinct positive values → Fin K indexed real menus retaining duplicates and a Borel probability law carried by a positive bounded interval, non-Dirac in part (a); reason: index sets retain every tie; for these real probability laws non-Dirac is exactly nontrivial support
--   - encoding: equation (2) is an expectation under the current normal belief and the update uses its estimated squared scale → a Gaussian Bochner integral with variance (s²).toNNReal and nextSd evaluated at its nonnegative square root; reason: this represents the same estimate; once the post is fixed the unknown-accuracy outer expectation is deterministic
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627, https://ssrn.com/abstract=3385627, supplied PDF created 2020-04-05, SHA256 58d685a3d44192b751d84a3068d681206ddf992c17423e0c4e138ebf661a5517, p. 10 (PDF 10), Proposition 1(a) and (b); §3 model pp. 7–9 (PDF 7–9); §4 proof pp. 10–11 (PDF 10–11).

import Definitions.Def_InfoInundation_CompleteScreening_EstimatedAccuracy

namespace InfoInundation.CompleteScreening

open MeasureTheory InfoInundation.Screening

/-- Proposition 1(a) and (b), p. 10, including both ex-post accuracy cases
specified on pp. 8–9 and explicitly included by the paragraph before the
proposition. Both the printed sd score and the prose variance reading are
asserted. Arbitrary positive-sd states include every reachable source state;
the empty menu is also allowed. No ranking or moment identity is assumed. -/
theorem proposition_1_all_accuracy_cases
    (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s)
    {K : ℕ} (Z : Fin K → ℝ) :
    ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
      argmaxMenu (sdScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (varScore G μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownSdScore μ s) Z = closestPosts μ Z ∧
      argmaxMenu (unknownVarScore μ s) Z = closestPosts μ Z) ∧
    (∀ σ : ℝ, 0 < σ → G = Measure.dirac σ →
      argmaxMenu (sdScore G μ s) Z = Finset.univ ∧
      argmaxMenu (varScore G μ s) Z = Finset.univ) := by sorry

end InfoInundation.CompleteScreening
