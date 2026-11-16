-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_subexponential_cost_characterization
-- name    : GoldreichAffine.Exponential.Supplement.subexponential_cost_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:13.738284+00:00
-- url     : https://prove2.me/theorems/267086f7-0963-47fa-85c3-658bcb6455c0
-- title:
--   Theorem 2 — subexponential cost iff bit-fixing affine advantage tends to 1/2
-- statement:
--   Let $(M_b)_{b\ge1}$ be any family of Boolean predicates, $M_b$ on $b$ inputs, and fix reals $s>1$ and $\gamma>0$. Set $m=\lceil n^s\rceil$ output bits and nonlinear arity $b=\lceil\gamma\log_2 n\rceil$, let $W_n=\{w\le n:|w-n/2|\le\sqrt{n\ln n}\}$, and let $C^\star(n,w;\gamma)$ be the optimal idealized cost of the guess-and-affine-approximation attack (Eq. (6)) against a seed of weight $w$. Then
--
--   $$C^\star(n,w;\gamma)=2^{o(n)}\ \text{ uniformly over } w\in W_n
--   \quad\Longleftrightarrow\quad
--   \lim_{b\to\infty}\operatorname{adv}_{\lceil\theta b\rceil}(M_b)=\frac12\ \text{ for every fixed }\theta\in(0,1).$$
--
--   The left side means: for every $\varepsilon>0$ there is $N$ such that for all $n\ge N$ the size parameters are valid and $\log_2C^\star(n,w;\gamma)\le\varepsilon n$ for every $w\in W_n$.
--
--   This companion theorem characterizes the subexponential regime of the cost model, complementing the mission's goal (Theorem 1), which characterizes the exponential regime.
--
--   Differences from the source:
--   - encoding: m = n^s, b = γ log₂ n and θb with integers implicitly rounded up → m = ⌈n^s⌉, b = ⌈γ log₂ n⌉, ⌈θb⌉ (the published base regime); reason: the paper's rounding convention of §2; the same definitions as the published goal
--   - encoding: C⋆(n,w;γ) = 2^{o(n)}, uniformly over w ∈ W_n (§3.3) → ∀ε>0 ∃N ∀n≥N, ValidSize s γ n ∧ ∀w ∈ W_n, log₂ C⋆ ≤ εn, with N before w; reason: log₂ C⋆ ≥ 0 holds in the cost model (C⋆ ≥ 1, App. A.5), so only the upper estimate carries content; ValidSize holds for all large n when s>1, γ>0
--   - encoding: γ > 0 a fixed constant of §3.3 → γ quantified outside the iff, with 0 < γ; reason: the theorem holds for each fixed γ (App. A.5: 'the argument holds for every fixed γ > 0')
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 8 (PDF p. 9), Theorem 2; proof App. A.5, pp. 21–22 (PDF pp. 22–23)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Regimes
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Theorem 2, printed p.8 / PDF p.9 (proof App. A.5, PDF pp.22–23): for each fixed gamma > 0,
    C*(n,w;gamma) = 2^{o(n)} uniformly over W_n iff adv_{theta b}(M_b) → 1/2 for every theta in (0,1). -/
theorem subexponential_cost_characterization (M : PredicateFamily) (s γ : ℝ)
    (hs : 1 < s) (hγ : 0 < γ) :
    SubexponentialCost M s γ ↔ NearHalfAdvantage M := by sorry

end GoldreichAffine.Exponential.Supplement
