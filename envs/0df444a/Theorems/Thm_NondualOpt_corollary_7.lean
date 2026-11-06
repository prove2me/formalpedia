-- Prove2me | Theorems.Thm_NondualOpt_corollary_7
-- name    : NondualOpt.corollary_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:30.853562+00:00
-- url     : https://prove2.me/theorems/1ab1ffd7-9a84-47b2-a1d9-7d9104202bcc
-- title:
--   Corollary 7 — first-order optimization bound $\tilde O_{p,q}(T^{-(1/p-(1/q-1/2)_+)})$ on $B_p^d$
-- statement:
--   Let $1\le p\le q\le\infty$ and $\theta=\frac1p-(\frac1q-\frac12)_+$. There are constants $C>0$ and $k\ge0$ depending only on $(p,q)$ such that for all $d,T\ge1$ there is a deterministic algorithm with the following property. For every convex $f:\mathbb R^d\to\mathbb R$ that is $1$-Lipschitz in $\|\cdot\|_q$ and every adaptive first-order oracle for $f$, after $T$ queries in $B_p^d$ the algorithm outputs $\hat x_T\in B_p^d$ with
--   $$
--   f(\hat x_T)-\min_{u\in B_p^d}f(u)\le C\,\log^k(e\,d\,T)\,T^{-\theta}=\tilde O_{p,q}\Big(\frac1{T^{1/p-(1/q-1/2)_+}}\Big).
--   $$
--   The oracle answers a query $x\in B_p^d$ with $f(x)$ and a vector $g$ with $\|g\|_{q^*}\le1$ and $f(y)\ge f(x)+\langle g,y-x\rangle$ for all $y\in B_p^d$.
--
--   For $p\le q$ and $T\le d$ this nearly matches the known lower bounds and improves on the rates of mirror descent: the deterministic method minimizes the max-regret of the oracle's affine minorants instead of the ordinary regret.
--
--   Differences from the source:
--   - generalization: §2's standing normalization f(0) = 0 → no normalization; reason: the class F of Corollary 7 is all convex 1-Lipschitz f; an algorithm may spend one query at 0 and run the (T − 1)-query method on f − f(0), and the constants absorb this
--   - generalization: a first-order oracle returning f(x) and a subgradient g ∈ ∂f(x) → any adaptive answer g with ‖g‖_{q∗} ≤ 1 and f(y) ≥ f(x) + ⟨g, y − x⟩ for y ∈ B_p^d; reason: this is the §2 oracle (g ∈ ∂f(x) ∩ H in the sense of (3)); it contains every oracle returning ordinary subgradients of a ‖·‖_q-1-Lipschitz convex f
--   - reading: Õ_{p,q}(T^{−θ}) → ∃ C > 0, k ≥ 0 depending only on (p, q), ∀ d, T ≥ 1, error ≤ C log(e d T)^k T^{−θ}; reason: §2, p.7: Õ omits logarithmic factors in d and T, O_ϑ allows ϑ-dependent constants
--   - encoding: min_{u ∈ B_p^d} f(u); d, T ∈ ℕ; ‖·‖_{q∗} → the bound for every u ∈ B_p^d; d, T ≥ 1; the conjugate exponent as an argument qs with q⁻¹ + qs⁻¹ = 1; reason: the minimum exists; T^{−θ} and log(edT) need d, T ≥ 1
--   - encoding: a deterministic algorithm computing x̂_T after T queries → a structure of query and output maps of the past answers, with queries and output in B_p^d, fixed before f and the oracle; reason: §2: ALG outputs x̂_T ∈ X, queries x ∈ X
--   - encoding: an adaptive oracle valid along the run → a map of the round, the past answers and the query, valid at every round, every history and every feasible query; reason: a valid answer exists at every feasible point of a convex ‖·‖_q-1-Lipschitz f, so an oracle valid along a run extends to such a map with the same transcript
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Corollary 7, p.12

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_theta
import Definitions.Def_NondualOpt_FOAlgorithm
import Definitions.Def_NondualOpt_IsValidOracle
import Definitions.Def_NondualOpt_transcript

open scoped ENNReal

namespace NondualOpt

/-- **Corollary 7 (First-order optimization bound).** Let `1 ≤ p ≤ q ≤ ∞`, `d, T ∈ ℕ`, and `F` the
class of convex functions `ℝ^d → ℝ` that are 1-Lipschitz in `‖·‖_q`. There is a deterministic
algorithm that for any `f ∈ F`, after `T` queries to a first-order oracle, computes `x̂_T` with
`f(x̂_T) − min_{u ∈ B_p^d} f(u) = Õ_{p,q}(1/T^{1/p − (1/q − 1/2)₊})`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Corollary 7, p.12.

**Formalization Note.** (i) `Õ_{p,q}(T^{−θ})` is: constants `C > 0`, `k ≥ 0` depending only on
`(p, q)`, chosen before `d` and `T`, with error `≤ C log(e·d·T)^k T^{−θ}` for every `d, T ≥ 1`
(§2, p.7: `Õ` omits logarithmic factors in `d` and `T`). (ii) The algorithm is fixed before `f`
and the oracle; its queries and output lie in `B_p^d`. (iii) The oracle is any adaptive §2 oracle:
at a query `x ∈ B_p^d` it returns `f(x)` and some `g` with `‖g‖_{q∗} ≤ 1` and
`f(y) ≥ f(x) + ⟨g, y − x⟩` for all `y ∈ B_p^d` (`qs` is the conjugate exponent `q∗`). (iv) The
standing normalization `f(0) = 0` of §2 is not assumed. (v) `min_{u ∈ B_p^d} f(u)` is replaced by
"for every `u ∈ B_p^d`" (the minimum exists). -/
theorem corollary_7 (p q qs : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) (hqs : q⁻¹ + qs⁻¹ = 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ d T : ℕ, 1 ≤ d → 1 ≤ T →
      ∃ A : FOAlgorithm d T p, ∀ f : (Fin d → ℝ) → ℝ, ConvexOn ℝ Set.univ f →
        (∀ x y, |f x - f y| ≤ RegimeDRCVaR.normM q (x - y)) →
        ∀ O : (t : Fin T) → (Fin t → ℝ × (Fin d → ℝ)) → (Fin d → ℝ) → (Fin d → ℝ),
          IsValidOracle p qs f O →
          ∀ u ∈ lpBall p d,
            f (A.output (transcript A f O T le_rfl)) - f u ≤
              C * Real.log (Real.exp 1 * d * T) ^ k * (T : ℝ) ^ (-theta p q) := by sorry

end NondualOpt
