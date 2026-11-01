-- Prove2me | Theorems.Thm_MaxObjBandit_proposition_1
-- name    : MaxObjBandit.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:39.607189+00:00
-- url     : https://prove2.me/theorems/a87150ad-45a3-436a-b291-e76d340db39b
-- title:
--   Proposition 1 — the best achievable max objective is $\mu_1T$
-- statement:
--   Let $\boldsymbol\nu\in\mathcal V$ be a bandit instance with $K\ge1$ arms and let $\mu_1=\max_i\mu_i$ be the highest mean. Then for every horizon $T$,
--   $$
--   \sup_{\pi\in\Pi_T}\mathcal R_T(\pi,\boldsymbol\nu)=\mathcal R^*_T(\boldsymbol\nu)=\mu_1T .
--   $$
--
--   The policy that always plays an arm of highest mean attains $\mu_1T$, and no policy does better. This identity rewrites the regret as $\mu_1T-\mathcal R_T(\pi,\boldsymbol\nu)$ in the proof of Theorem 4.
--
--   Differences from the source:
--   - encoding: $\mathcal R^*_T(\boldsymbol\nu)=\mu_1T$ with arms relabelled so that $\mu_1$ is the highest mean → $(\max_i\mu_i)\,T$ (`⨆ i, ν.mean i`), arms not relabelled; reason: the same value without relabelling
--   - reading: $\Pi_T$ is the set of all mappings from histories to arms → policies whose decision rules are measurable (`IsMeasurablePolicy`); reason: p.16 says that once a policy is fixed, $I_t$, $X_t$ and $n^i_t$ become well-defined random variables, which requires measurability; for a non-measurable rule $\mathcal R_T$ is undefined
--   - encoding: arms $1,\dots,K$ and rewards $U^i_n$ indexed from $n=1$ → arms `Fin K` (paper arm $i$ is index $i-1$) and a reward table `Fin K → ℕ → ℝ` with `ω i n` $=U^i_{n+1}$; reason: Lean indexing convention; the same objects
--   - encoding: a bandit with $K$ arms → `0 < K`; reason: a bandit has at least one arm; $\mu_1$ is undefined for $K=0$
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, Proposition 1, p.16 (proof in Appendix A.1, p.52)

import Mathlib
import Definitions.Def_MaxObjBandit_regret

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- **Proposition 1** (arXiv:2006.06853v6, Proposition 1, p.16; proof in Appendix A.1, p.52).
For any bandit instance `ν ∈ 𝒱`, `sup_{π∈Π_T} R_T(π, ν) = R*_T(ν) = µ₁T`, where `µ₁` is the highest
mean.

**Formalization Note** The arms are not sorted, so `µ₁ = maxᵢ µᵢ` is written `⨆ i, ν.mean i`. `Π_T`
is the set of policies with measurable decision rules (`optimum`). `0 < K`: a bandit has at least
one arm. -/
theorem proposition_1 {K : ℕ} (hK : 0 < K) (ν : BanditInstance K) (T : ℕ) :
    optimum ν T = (⨆ i, ν.mean i) * T := by sorry

end MaxObjBandit
