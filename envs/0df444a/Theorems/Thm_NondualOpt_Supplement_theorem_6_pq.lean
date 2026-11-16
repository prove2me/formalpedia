-- Prove2me | Theorems.Thm_NondualOpt_Supplement_theorem_6_pq
-- name    : NondualOpt.Supplement.theorem_6_pq
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:14:38.561306+00:00
-- url     : https://prove2.me/theorems/6d1f195c-2d50-4285-9a64-54ad09e177cf
-- title:
--   Theorem 6 ($(p,q)$ clause) — $V^{\max}_{p,q^*,T}/T\asymp_{p,q}T^{-(1/p-(1/q-1/2)_+)}$ up to logarithms, for $p\le q$, $T\le d$
-- statement:
--   Let $1\le p\le q\le\infty$, let $q^*$ be the conjugate exponent of $q$, and set $\theta=\theta(p,q)=\frac1p-\big(\frac1q-\frac12\big)_+$. Let $V^{\max}_{p,q^*,T}$ be the minimax value of the $T$-round affine max-regret game with decision set $X=B_p^d$ and loss slopes in $H=B_{q^*}^d$. There are constants $c,C>0$ and $k\ge0$, depending only on $p$ and $q$, such that for all integers $d,T$ with $1\le T\le d$,
--   $$
--   \frac{c}{T^{\theta}}\ \le\ \frac{V^{\max}_{p,q^*,T}}{T}\ \le\ \frac{C\,\log(edT)^k}{T^{\theta}}.
--   $$
--   That is, $T^{-\theta}\lesssim_{p,q}V^{\max}_{p,q^*,T}/T=\tilde O_{p,q}(T^{-\theta})$.
--
--   This is the $(p,q)$-norm specialization of Theorem 6 in the high-dimensional regime $T\le d$: combined with the max-regret online-to-batch conversion it yields Corollary 7, and its lower half shows that the max-regret value cannot give a better rate.
--
--   **Formalization Note** Both sides are multiplied by $T$ and compared as extended reals; $V^{\max}$ is the published `NondualOpt.Vmax` for the dot product.
--
--   Differences from the source:
--   - encoding: $1/T^{\theta}\lesssim_{p,q}V^{\max}_{p,q^*,T}/T=\tilde O_{p,q}(1/T^{\theta})$ → constants $c,C>0$, $k\ge0$ depending only on $(p,q)$, chosen before $d$ and $T$, with $cT\cdot T^{-\theta}\le V^{\max}\le CT\log(edT)^kT^{-\theta}$; reason: §2 (p.7) reads $O_\vartheta$ as constants depending only on $\vartheta$ and $\tilde O$ as omitting logarithmic factors in $d$ and $T$; the same reading as the published Corollary 7
--   - encoding: bounds on $V^{\max}/T$ → bounds on $V^{\max}$ multiplied by $T$, compared as extended reals; reason: $T\ge1$; the published $V^{\max}$ is extended-real valued; same instances
--   - encoding: $q^*$ → an exponent $q_*$ with $q^{-1}+q_*^{-1}=1$; reason: the conjugate exponent as in the published items
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 6, p.12 ("Thus, if p ≤ q and T ≤ d, then …"; T ≥ 1 from the theorem, p.11)

import Mathlib
import Definitions.Def_NondualOpt_theta
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_Vmax

open scoped ENNReal

namespace NondualOpt.Supplement

/-- **Theorem 6, the `(p, q)` clause.** For `1 ≤ p ≤ q ≤ ∞` and `1 ≤ T ≤ d`, with
`θ = 1/p − (1/q − 1/2)₊`,
`1/T^θ ≲_{p,q} V^max_{p,q∗,T}/T = Õ_{p,q}(1/T^θ)`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 6, p.12 ("Thus, if `p ≤ q` and
`T ≤ d`, then …"; the theorem's standing `T ≥ 1`, p.11).

**Formalization Note.** (i) `V^max_{p,q∗,T}` is the published `NondualOpt.Vmax` of the affine
max-regret game for `(X, H) = (B_p^d, B_{q∗}^d)` with the dot product; `qs` is the conjugate
exponent `q∗` (`q⁻¹ + qs⁻¹ = 1`). (ii) `≲_{p,q}` and `Õ_{p,q}` are read as constants `c, C > 0`,
`k ≥ 0` depending only on `(p, q)`, chosen before `d` and `T`; `Õ` omits the factor
`log(e·d·T)^k` (§2, p.7: logarithmic factors in `d` and `T`), as in the published
`NondualOpt.corollary_7`. The lower bound carries no logarithm. (iii) Both sides are multiplied
by `T` and compared in `EReal`. -/
theorem theorem_6_pq (p q qs : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) (hqs : q⁻¹ + qs⁻¹ = 1) :
    ∃ c C k : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ k ∧ ∀ d T : ℕ, 1 ≤ T → T ≤ d →
      (((c * T * (T : ℝ) ^ (-theta p q) : ℝ) : EReal) ≤
          Vmax (dotPair d) (lpBall p d) (lpBall qs d) T) ∧
        Vmax (dotPair d) (lpBall p d) (lpBall qs d) T ≤
          ((C * T * Real.log (Real.exp 1 * d * T) ^ k * (T : ℝ) ^ (-theta p q) : ℝ) : EReal) := by sorry

end NondualOpt.Supplement
