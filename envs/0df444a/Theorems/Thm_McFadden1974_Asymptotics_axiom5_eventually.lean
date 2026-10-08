-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_axiom5_eventually
-- name    : McFadden1974.Asymptotics.axiom5_eventually
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:47:42.804997+00:00
-- url     : https://prove2.me/theorems/2e54adae-6b00-4d6e-ae2b-582ad9b79368
-- title:
--   Lemma 5, proof — Axiom 7 implies Axiom 5 (full rank) for large samples
-- statement:
--   Consider a serially indexed conditional logit sample with data $z_{im}\in\mathbb R^K$ satisfying **Axiom 7**: the numbers of alternatives and the vectors $z_{im}$ are uniformly bounded, and the averaged moment matrices $\frac1q\sum_{m<q}\Omega_m(\theta^0)$ converge to a positive definite matrix $\Omega$. Then **Axiom 5** holds for all large samples: there is $q_0$ such that for every $q \ge q_0$ the vectors
--   $$z_{im} - \bar z_m(\theta^0), \qquad m < q,\ 1 \le i \le J_m,$$
--   span $\mathbb R^K$; equivalently, the matrix with these rows has rank $K$.
--
--   Axiom 5 makes the Hessian of the log-likelihood negative definite, so the likelihood has at most one maximizer. This result shows that the asymptotic condition of Axiom 7 implies it in every sufficiently large sample.
--
--   **Formalization Note** The means $\bar z_m$ are evaluated at $\theta^0$; the span does not depend on that choice.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 134, Lemma 5, proof (first sentence); also p. 120 (remark after Axiom 7); PDF pp. 30, 16

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Axiom 7 implies Axiom 5 for large samples** (Lemma 5, proof, p. 134, PDF p. 30: "As noted
in the text, Axiom 7 implies that Axiom 5 holds when Σ_{n=1}^N R_n is large"; p. 120, PDF p. 16:
"The last part of this axiom strengthens the full-rank condition assumed earlier"). Axiom 5
(p. 116, PDF p. 12) asks that the matrix whose rows are the vectors `z_in − z̄_n` be of rank
`K`, i.e. that these vectors span `ℝ^K`.

Formalization Note: rank `K` of the matrix with rows `z_{im} − z̄_m` (`m < q`, all `i`) is
stated as: these vectors span `EuclideanSpace ℝ (Fin K)`. The means `z̄_m` are taken at `θ⁰`;
the span does not depend on the parameter at which `z̄_m` is evaluated, since it equals the
span of the differences `z_{im} − z_{jm}`. Only Axiom 7 is used; no randomness is involved. -/
theorem axiom5_eventually {K : ℕ} (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀,
      Submodule.span ℝ {v | ∃ m < q, ∃ i : Fin (D.J m), v = D.z m i - zbar D m θ₀} = ⊤ := by sorry

end McFadden1974.Asymptotics
