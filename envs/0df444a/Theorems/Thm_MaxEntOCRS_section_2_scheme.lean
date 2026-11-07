-- Prove2me | Theorems.Thm_MaxEntOCRS_section_2_scheme
-- name    : MaxEntOCRS.section_2_scheme
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:30.16253+00:00
-- url     : https://prove2.me/theorems/9af5a96b-5789-464c-9660-8c9b0f9b3be6
-- title:
--   Section 2 — the simulate-then-replace scheme: $\Pr(e\in M) = \theta_e\Pr[\mathrm{Add}(e)]$, acceptance $\le 1$ iff $\Pr[\mathrm{Add}(e)] \ge \alpha'$, and the law $\mu^*$ is kept
-- statement:
--   Let $x \in P(G)$, $\alpha' \in (0, 1)$, and let $\mu^*$ be the monomer–dimer (Gibbs) measure of $G$ with activities $t \ge 0$ whose edge marginals are $\alpha' x$. Put $\theta_e = t_e/(1 + t_e)$. Then
--
--   1. $\Pr_{\mu^*}(e \in M) = \theta_e \Pr_{\mu^*}[\mathrm{Add}(e)]$ for every edge $e$;
--   2. for every edge with $x_e > 0$, the acceptance probability $\theta_e/x_e$ is at most $1$ exactly when $\Pr_{\mu^*}[\mathrm{Add}(e)] \ge \alpha'$;
--   3. every step of the simulate-then-replace scheme started from $\mu^*$ keeps the law $\mu^*$;
--   4. consequently the law $\mu^*$ is kept after any sequence of arrivals, whatever the order.
--
--   This is why the template is $\alpha'$-selectable and stationary whenever every edge is addable with probability at least $\alpha'$.
--
--   Differences from the source:
--   - generalization: the matching then keeps the law µ* after every step, whatever the order (in the case Pr[Add(e)] ≥ α′) → every step and every list of arrivals (repetitions and omissions allowed) keeps µ*, with no condition on Pr[Add(e)]; reason: the law identity is algebraic once the insertion probability is θ_e; the paper's case is included
--   - encoding: the scheme as a randomized online procedure, acceptance probability θ_e/x_e → a law transform with one Bernoulli(x_e) activation per arrival; acceptance written Pr(e ∈ M)/(x_e Pr[Add(e)]); reason: activations are independent and revealed at arrival; equals θ_e/x_e by clause 1
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_OnlineCRS_Matching_Model
import Definitions.Def_MaxEntOCRS_edgeMarginal
import Definitions.Def_MaxEntOCRS_addProb
import Definitions.Def_MaxEntOCRS_monomerDimer
import Definitions.Def_MaxEntOCRS_acceptProb
import Definitions.Def_MaxEntOCRS_schemeStep
import Definitions.Def_MaxEntOCRS_schemeLaw

namespace MaxEntOCRS

/-- The simulate-then-replace scheme run from a Gibbs measure (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). Let `x ∈ P(G)`,
`α′ ∈ (0, 1)`, and let `µ*` be the monomer–dimer measure with nonnegative activities `t`
whose edge marginals are `α′x`; put `θ_e = t_e/(1 + t_e)`. Then (i) `Pr_µ*(e ∈ M) =
θ_e Pr_µ*[Add(e)]`; (ii) for `x_e > 0` the acceptance probability `θ_e/x_e` is at most `1`
exactly when `Pr_µ*[Add(e)] ≥ α′`; (iii) every step keeps the law `µ*`; and (iv) so does every
sequence of steps, whatever the order. -/
theorem section_2_scheme {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (hx : x ∈ OnlineCRS.Matching.matchingRelax G) (α' : ℝ) (hα'0 : 0 < α') (hα'1 : α' < 1)
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e)
    (hmarg : ∀ e, edgeMarginal (monomerDimer G t) e = α' * x e) :
    (∀ e, edgeMarginal (monomerDimer G t) e = t e / (1 + t e) * addProb G (monomerDimer G t) e) ∧
      (∀ e, 0 < x e →
        (acceptProb G x (monomerDimer G t) e ≤ 1 ↔ α' ≤ addProb G (monomerDimer G t) e)) ∧
      (∀ e, schemeStep G x (monomerDimer G t) e (monomerDimer G t) = monomerDimer G t) ∧
      ∀ σ : List E, schemeLaw G x (monomerDimer G t) σ = monomerDimer G t := by sorry

end MaxEntOCRS
