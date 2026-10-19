-- Prove2me | Theorems.Thm_OAI_Erdos3_approxProduct_low_degree_step_s2
-- name    : OAI.Erdos3.approxProduct_low_degree_step_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:22:41.171536+00:00
-- url     : https://prove2.me/theorems/b31e1921-5128-4e0f-95a1-67650e2c3364
-- title:
--   Inductive step bounding the degree-k ANOVA energy of a density times a bounded function on an approximate product space
-- statement:
--   Let $I$ be a finite linearly ordered type, $X_i$ ($i \in I$) finite types, and $\mu_i$ a `FiniteProbabilityWeights (X i)` (a probability weight vector on $X_i$, defined by OpenAI) for each $i$; write $\mu = \prod_i \mu_i$ for the product weights on $\prod_i X_i$. Let $k, r, q$ be natural numbers with $0 < k \le r$, $q \ge 2$ and $q$ even. Let `base` $\in \prod_i X_i$ and $x_0 \in \Sigma_i X_i$. Let $K, M, R, \eta$ be real numbers with $K \ge 1$, $M \ge 0$, $\eta \ge 0$, $1 + K \le R$, $\log(2 + M) \le q$, $2e\,(qk)^{k} \le R^{2k}$, and
--   $$\eta\cdot\bigl(\texttt{approxMomentEnvelope}\ |I|\ r\ M\bigr)^{q} \le \tfrac12,\qquad \texttt{approxMomentEnvelope}\ N\ r\ M = 2^{r+1}(2 + N)^{r}(2 + M).$$
--   Let $\rho, F : \prod_i X_i \to \mathbb{R}$ with $\rho(x) \ge 0$ and $0 \le F(x) \le M$ for all $x$. Suppose:
--
--   - `ProductMarginalsClose μ ρ η (r (q + 1))`: for every set $B \subseteq I$ with $|B| \le r(q+1)$ and every $x$ with $\mu(x) \ne 0$, the conditional mean `productConditionalMean μ B ρ x` (defined by OpenAI: the $\mu$-average of $\rho$ over the coordinates outside $B$, with the coordinates in $B$ fixed to those of $x$) is within $\eta$ of $1$;
--   - `ProductBoundedMarginals μ (ρ F) K r`: for every $J \subseteq I$ with $|J| \le r$ and every $x$ with $\mu(x) \ne 0$, `productConditionalMean μ J (ρ F) x` $\le K^{|J|}$;
--   - for every $T \subseteq I$ with $0 < |T| \le k$, every $a$ with $\mu(a) \ne 0$ and every $A \subseteq T$,
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{P}_{k - |T|}\ \bigl(\texttt{productNormalizedSection}\ \mu\ T\ A\ a\ K\ (\rho F)\bigr)} \le R^{2(k - |T|)},$$
--   where $\mathcal{P}_\ell$ is the family of all subsets of $I$ of size $\ell$, `productANOVAEnergy μ D g` $= \sum_{S \in D} \mathbb{E}_{\mu}\bigl[(g_S)^2\bigr]$ is the energy of the ANOVA (Efron–Stein) components $g_S$ = `productANOVA μ S g` of $g$ indexed by $D$, and `productNormalizedSection μ T A a K g` $= K^{-|A|}\cdot$`productSectionAverage μ T A a g` (a section average defined by OpenAI).
--
--   Then
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{P}_{k}\ (\rho F)} \le R^{2k}.$$
--
--   Lean: `OAI.Erdos3.approxProduct_low_degree_step_s2`, which states OpenAI's `OAI.Erdos3.approxProduct_low_degree_step` (in `lean/OAI/Combinatorics/Progressions/Polynomial/FiniteMarginalLowDegree.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B127`, `OAIE3v2B139` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/FiniteMarginalLowDegree.lean (declaration OAI.Erdos3.approxProduct_low_degree_step)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B139

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_step_s2 (k r q : ℕ) (hk : 0 < k) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) (base : ∀ i, X i) (x₀ : Sigma X)
    {K M R eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta) (hR : 1 + K ≤ R)
    (hlog : Real.log (2 + M) ≤ (q : ℝ))
    (hcoeff : 2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ R ^ (2 * k))
    (hbudget : eta * approxMomentEnvelope (Fintype.card I) r M ^ q ≤ 1 / 2)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ k → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - T.card))
          (productNormalizedSection μ T A a K (fun x => rho x * F x))) ≤ R ^ (2 * (k - T.card))) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤ R ^ (2 * k) := by
  sorry

end Erdos3

end

end OAI
end
