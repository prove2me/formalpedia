-- Prove2me | Theorems.Thm_NetworkDuopoly_Asymmetry_proposition_4
-- name    : NetworkDuopoly.Asymmetry.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:54.771114+00:00
-- url     : https://prove2.me/theorems/d2d483e0-6698-4d6d-b5ed-602508a90513
-- title:
--   Proposition 4 — exactly two asymmetric equilibria at low quality
-- statement:
--   Consider the two-firm Cournot game with common quality $\alpha\in\mathbb R$, homogeneous network strength $\gamma\ge0$, and shares $x,y\in[0,1]$, each uniform across customers. The firms receive $R_{\alpha,\gamma}(x,y)$ and $R_{\alpha,\gamma}(y,x)$, where $R$ is the normalized revenue with zero payoff at own share zero and $-\infty$ for positive own share at or beyond full market coverage. Let $\operatorname{NE}_{\alpha,\gamma}(x,y)$ mean mutual global best responses over all unilateral shares in $[0,1]$.
--
--   There exist a real $\alpha_0$ and real-valued functions $\underline\Gamma,\overline\Gamma:\mathbb R\to\mathbb R$ such that, for every $\alpha<\alpha_0$,
--   $$0\le\underline\Gamma(\alpha)<\overline\Gamma(\alpha),$$
--   and for every $\underline\Gamma(\alpha)<\gamma<\overline\Gamma(\alpha)$ there exist $a,b$ with $0<a<b$ and $a+b<1$ satisfying
--   $$
--   \forall x,y\in\mathbb R,\qquad
--   \operatorname{NE}_{\alpha,\gamma}(x,y)
--   \ \Longleftrightarrow\ (x,y)=(a,b)\ \text{or}\ (x,y)=(b,a).
--   $$
--   Thus there are exactly two pure Nash equilibria and both are asymmetric, even though the two firms have identical primitives. The statement excludes every additional equilibrium, including any symmetric one.
--
--   **Formalization Note** Assumptions 1–3 are implemented by the concrete scalar game: $n\ge1$, common $\beta>0$, all $g_{ij}=\gamma/(2n)$ including the diagonal, customer-uniform strategies and equal qualities. Dividing actual revenue by the positive factor $n/\beta$ preserves all best responses. The thresholds are finite real functions depending only on $\alpha$; their nonempty positive interval cannot depend on an equilibrium or on $\gamma$. Neither the rounded $-1.98$ nor the proof's numerical $-15.2$ is fixed. The full exact-count conclusion is retained despite the proof issues documented in findings F1–F2.
-- source:
--   Chen and Chen (2021), Duopoly Competition with Network Effects in Discrete Choice Models, https://doi.org/10.1287/opre.2020.2079; supplied artifact p. 22 (PDF 22), Proposition 4; Assumptions 1–3 on pp. 15, 17; proof pp. ec6–ec16 (PDF 50–60).

import Definitions.Def_NetworkDuopoly_Asymmetry_bestResponse

namespace NetworkDuopoly.Asymmetry

/- Imported declaration bodies (verbatim), included for standalone audit.
noncomputable def revenue (α γ x y : ℝ) : EReal :=
  if x = 0 then 0
  else if 0 < x ∧ x + y < 1 then
    ((x * (α + γ * x / 2 - Real.log x + Real.log (1 - x - y)) : ℝ) : EReal)
  else ⊥

def bestResponse (α γ y : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ u ∈ Set.Icc (0 : ℝ) 1, revenue α γ u y ≤ revenue α γ x y}

def IsEquilibrium (α γ x y : ℝ) : Prop :=
  x ∈ bestResponse α γ y ∧ y ∈ bestResponse α γ x
-/

theorem proposition_4 :
    ∃ (α₀ : ℝ) (Γlo Γhi : ℝ → ℝ),
      ∀ α : ℝ, α < α₀ →
        0 ≤ Γlo α ∧ Γlo α < Γhi α ∧
        ∀ γ : ℝ, Γlo α < γ → γ < Γhi α →
          ∃ a b : ℝ, 0 < a ∧ a < b ∧ a + b < 1 ∧
            ∀ x y : ℝ, IsEquilibrium α γ x y ↔
              (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by sorry

end NetworkDuopoly.Asymmetry
