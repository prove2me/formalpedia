-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_3_3
-- name    : LogSupermodularBIS.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:56.29686+00:00
-- url     : https://prove2.me/theorems/424358f5-b361-4d23-8408-5e4f67b76a69
-- title:
--   Lemma 3.3 — entropy identity for threshold descents
-- statement:
--   Let $\Phi$ be a potential on $\{0,1\}^d$ with $\Phi(0)=0$ and $\mu=e^\Phi/Z_\Phi$. For every branching rule $\theta$, the threshold descent $f^\theta$ takes values in $\{0,1\}^d$, its $i$th coordinate depends only on $U_1,\dots,U_i$, and
--   $$E[a(U_i)f^\theta_i(U)\mid U_{<i}]=H\bigl(\theta_{f^\theta_{<i}(U)}\bigr)$$
--   for every $i$. Hence $\sum_iE[a(U_i)f^\theta_i(U)]=H(\nu_\theta)$, and adding $E\Phi(f^\theta(U))$ gives the bracket in (3.4). In particular $\sum_iE[a(U_i)f_i(U)]=H(\mu)$ for the exact guide $f$, and
--   $$\sum_{i=1}^dE[a(U_i)f_i(U)]+E\Phi(f(U))=\log Z_\Phi.$$
--
--   Differences from the source:
--   - encoding: E[a(U_i) f^θ_i(U) | U_{<i}] = H(θ_{f^θ_{<i}(U)}) → for every u ∈ (0,1)^d, ∫_{(0,1)} a(t) f^θ_i(u with u_i := t) dt = H(θ at the prefix reached by u); reason: f^θ_i depends only on U_{≤i}, so this integral is a version of the conditional expectation, here at every input
--   - encoding: coordinates and rows 1, …, d → Fin d, indices 0, …, d−1; reason: index shift only
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 15 (PDF 16), Lemma 3.3

import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Lemma 3.3 (Entropy identity for threshold descents), p. 15. The conditional expectation
given `U_{<i}` is stated as the integral over the fresh input `U_i = t`, at every input. -/
theorem lemma_3_3 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0)
    (θ : List Bool → ℝ) (hθ : IsBranchingRule d θ) :
    (∀ (u : Fin d → ℝ) (i : Fin d), thresholdDescent θ u i = 0 ∨ thresholdDescent θ u i = 1) ∧
    (∀ u u' : Fin d → ℝ, ∀ i : Fin d, (∀ j : Fin d, j ≤ i → u j = u' j) →
      thresholdDescent θ u i = thresholdDescent θ u' i) ∧
    (∀ u ∈ openCube d, ∀ i : Fin d,
      ∫ t in Set.Ioo (0 : ℝ) 1, logit t * thresholdDescent θ (Function.update u i t) i =
        H (θ (descentPrefix θ u i.val))) ∧
    linearScore (thresholdDescent (d := d) θ) = lawEntropy (leafLaw (d := d) θ) ∧
    linearScore (thresholdDescent (d := d) θ) +
        ∫ u, Φ (toConfig (thresholdDescent θ u)) ∂unifCube d = treeObjective Φ θ ∧
    linearScore (exactGuide Φ) = lawEntropy (potentialLaw Φ) ∧
    booleanObjective Φ (exactGuide Φ) = Real.log (potentialPartition Φ) := by sorry

end LogSupermodularBIS.Main
