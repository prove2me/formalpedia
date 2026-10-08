-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_theorem_3_5
-- name    : ManyServerFluid.Uniqueness.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:00.803496+00:00
-- url     : https://prove2.me/theorems/dc8b0288-fe5c-41cd-b5c0-97423d7e7b8f
-- title:
--   Theorem 3.5 — the fluid equations have at most one solution, characterized by (3.6), (3.7) and the representation (3.11); (3.12) for κ̄
-- statement:
--   Let $(\bar E, \bar X(0), \bar\nu_0) \in \mathcal S_0$.
--
--   1. **Uniqueness.** There is at most one solution $(\bar X, \bar\nu)$ to the associated fluid equations (3.4)–(3.7).
--   2. **Representation.** Let $(\bar X,\bar\nu)$ be càdlàg, $\bar X \ge 0$, $\bar\nu_t \in \mathcal M_{\le1}[0,M)$, starting at $(\bar X(0), \bar\nu_0)$, and let $\bar\nu$ satisfy (3.4). Then $(\bar X,\bar\nu)$ solves the fluid equations if and only if it satisfies (3.6), (3.7) and, for every $f \in \mathcal C_b(\mathbb R_+)$ and $t \ge 0$,
--   $$\int_{[0,M)} f(x)\,\bar\nu_t(dx) = \int_{[0,M)} f(x+t)\frac{1-G(x+t)}{1-G(x)}\,\bar\nu_0(dx) + \int_{[0,t]} f(t-s)\big(1-G(t-s)\big)\,d\bar K(s), \qquad (3.11)$$
--   with $\bar K$ given by (3.8).
--   3. **Entry rate.** If $\bar E$ is absolutely continuous with derivative a.e. equal to $\bar\lambda$, then $\bar K$ is absolutely continuous and its derivative $\bar\kappa$ satisfies, for a.e. $t \ge 0$,
--   $$\bar\kappa(t) = \begin{cases}\bar\lambda(t), & \bar X(t) < 1,\\ \bar\lambda(t)\wedge\langle h,\bar\nu_t\rangle, & \bar X(t) = 1,\\ \langle h,\bar\nu_t\rangle, & \bar X(t) > 1.\end{cases}\qquad(3.12)$$
--   4. **Densities.** If both $\bar\nu_0$ and $\bar E$ are absolutely continuous, then $\bar\nu_t$ is absolutely continuous for every $t \ge 0$.
--
--   The theorem shows that the fluid model of the $GI/G/N$ queue is well posed and gives its solution explicitly in terms of the entry process $\bar K$; (3.11) and (3.12) are the form in which the fluid limit is analysed in the rest of the paper.
--
--   **Formalization Note.** The paper's right-hand side of the equivalence lists (3.6) and (3.11); the nonidling condition (3.7), part of the fluid equations on the left, is kept on the right, as the proof requires (without it a pure-decay path with $\bar K \equiv 0$ would satisfy (3.6) and (3.11) for any $\bar E$). "Absolutely continuous with derivative $\bar\lambda$" is $\bar E(t) = \int_{[0,t]}\bar\lambda$ with $\bar\lambda$ integrable on bounded intervals; absolute continuity of $\bar K$ is the existence of such a $\bar\kappa$; absolute continuity of measures is with respect to Lebesgue measure. $\langle h,\bar\nu_t\rangle$ is the real value of the lower integral, finite for a.e. $t$ by (3.4). $f \in \mathcal C_b(\mathbb R_+)$ is a bounded continuous function on $\mathbb R$ (only values on $[0,\infty)$ are read). Uniqueness is stated as equality of the two solutions at every $t \ge 0$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 45, Theorem 3.5, (3.11)–(3.12)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

namespace ManyServerFluid.Uniqueness

/-- Theorem 3.5, p. 45. (i) For any (Ē, X̄(0), ν̄_0) ∈ S_0 the fluid equations have at most one
solution. (ii) For (X̄, ν̄) with the path properties of Definition 3.3 and (3.4), (X̄, ν̄) solves the
fluid equations iff it satisfies (3.6), (3.7) and the representation (3.11) for every f ∈ C_b(R₊)
(the paper's right-hand side lists (3.6) and (3.11); the nonidling condition (3.7), part of the
fluid equations on the left, is kept on the right, as the proof requires). (iii) If Ē is absolutely
continuous with density λ̄, then K̄ is absolutely continuous with density κ̄ given a.e. by (3.12).
(iv) If moreover ν̄_0 is absolutely continuous, every ν̄_t is. -/
theorem theorem_3_5 (S : ServiceLaw) :
    -- (i) uniqueness
    (∀ (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ), S.InS0 E X0 ν0 →
      ∀ (X₁ : ℝ → ℝ) (ν₁ : ℝ → FiniteMeasure ℝ) (X₂ : ℝ → ℝ) (ν₂ : ℝ → FiniteMeasure ℝ),
        S.IsFluidSolution E X0 ν0 X₁ ν₁ → S.IsFluidSolution E X0 ν0 X₂ ν₂ →
        ∀ t, 0 ≤ t → X₁ t = X₂ t ∧ ν₁ t = ν₂ t) ∧
    -- (ii) the representation (3.11)
    (∀ (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ),
      S.InS0 E X0 ν0 → ServiceLaw.IsCadlag X → ServiceLaw.IsCadlag ν →
      (∀ t, 0 ≤ t → 0 ≤ X t) → (∀ t, 0 ≤ t → S.IsSubProb (ν t)) →
      X 0 = X0 → ν 0 = ν0 → (∀ t, 0 ≤ t → S.hInt ν t < ⊤) →
      (S.IsFluidSolution E X0 ν0 X ν ↔
        (∀ t, 0 ≤ t → X t = X0 + E t - S.Dbar ν t) ∧
        (∀ t, 0 ≤ t → 1 - ((ν t).mass : ℝ) = max (1 - X t) 0) ∧
        ∀ f : ℝ →ᵇ ℝ, ∀ t, 0 ≤ t →
          ∫ x, f x ∂(ν t : Measure ℝ) =
            ∫ x, f (x + t) * ((1 - S.G (x + t)) / (1 - S.G x)) ∂(ν0 : Measure ℝ)
            + ∫ s in Icc 0 t, f (t - s) * (1 - S.G (t - s)) ∂(stieltjes (S.Kbar ν)))) ∧
    -- (iii) (3.12)
    (∀ (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
      (lam : ℝ → ℝ), S.InS0 E X0 ν0 → S.IsFluidSolution E X0 ν0 X ν →
      (∀ t, IntegrableOn lam (Icc 0 t)) → (∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s) →
      ∃ κ : ℝ → ℝ, (∀ t, IntegrableOn κ (Icc 0 t)) ∧
        (∀ t, 0 ≤ t → S.Kbar ν t = ∫ s in Icc 0 t, κ s) ∧
        ∀ᵐ t ∂(volume.restrict (Ici 0)),
          κ t = if X t < 1 then lam t
                else if X t = 1 then
                  min (lam t) (∫⁻ x, ENNReal.ofReal (S.h x) ∂(ν t : Measure ℝ)).toReal
                else (∫⁻ x, ENNReal.ofReal (S.h x) ∂(ν t : Measure ℝ)).toReal) ∧
    -- (iv) absolute continuity of ν̄_t
    (∀ (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
      (lam : ℝ → ℝ), S.InS0 E X0 ν0 → S.IsFluidSolution E X0 ν0 X ν →
      (∀ t, IntegrableOn lam (Icc 0 t)) → (∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s) →
      (ν0 : Measure ℝ) ≪ volume → ∀ t, 0 ≤ t → (ν t : Measure ℝ) ≪ volume) := by sorry

end ManyServerFluid.Uniqueness
