-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_uniform_to_fixed_weight_transfer
-- name    : GoldreichAffine.Exponential.uniform_to_fixed_weight_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:23.953008+00:00
-- url     : https://prove2.me/theorems/283eda85-316f-4985-834f-ea5fde013d2d
-- title:
--   Lemma 2 — uniform-to-fixed-weight transfer
-- statement:
--   Let $n,b\ge1$, $b\le n$, $0\le w\le n$, and let $(n′,w′)$ be a feasible reduced guess: $n′\le n$, $w′\le n′$ and $0\le w-w′\le n-n′$. Let $0\le b′\le\min(b,n′)$ and let $M$ be any $b$-bit predicate. Write $Z_j$ for the fixed-weight marginal from this guess and $\ell=\min(w′,n′-w′)$. Define
--   $$p_j=\frac{2^j\binom\ell j}{\binom{n′}{b′}}\sum_{h=0}^{\lfloor(b′-j)/2\rfloor}\binom{\ell-j}{h}\binom{n′-2\ell}{b′-j-2h},\quad\Phi(n′,w′,b′)=\sum_{j=0}^{b′}p_j\operatorname{adv}_j(M),$$
--   with $p_j=0$ for $j>\ell$. For every residual $Q\in\mathcal R_{b′}(M)$ and affine $f\in\mathcal A_{b′}$,
--   $$\Pr[Q(Z_{b′})=f(Z_{b′})]\le\tfrac12+\Phi(n′,w′,b′).$$
--   Consequently, every feasible overlap class $r$ satisfies
--   $$q_r\le\tfrac12+\Phi(n′,w′,b-r).$$
--   The statement retains both agreement bounds and the full pairing law, including $n′=b′=0$. It supplies the finite distribution transfer needed for the cost lower bound.
--
--   Differences from the source:
--   - encoding: a feasible global guess (R,u) → its feasible reduced parameters (n′,w′); reason: every pair with n′≤n, w′≤n′, w′≤w and w−w′≤n−n′ is realizable, and the source probabilities and costs depend only on this pair
--   - encoding: probabilities and finite maxima → finite nonnegative sums and maxima, with the class inequality embedded into nonnegative extended reals; reason: the exact fixed-weight law is normalized on the feasible domain and all values equal the source probabilities
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 14 (PDF p. 15), Lemma 2, Eqs. (9)–(11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_TransferBenefit
open scoped NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Lemma 2, printed p.14 / PDF p.15, both (10) and (11); (9) defines phi. -/
theorem uniform_to_fixed_weight_transfer {n w b np wp bp : ℕ} (M : Predicate b)
    (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n) (hw : w ≤ n)
    (hguess : FeasiblePair n w np wp) (hbp : bp ≤ min b np) :
    (∀ (Q f : Predicate bp), IsResidual M Q → IsAffine f →
      fixedAgreement np wp Q f ≤ 1 / 2 + phi M np wp bp) ∧
    (∀ r ∈ overlaps n b np,
      reliability M np wp r ≤ ENNReal.ofReal (1 / 2 + phi M np wp (b - r))) := by sorry

end GoldreichAffine.Exponential
