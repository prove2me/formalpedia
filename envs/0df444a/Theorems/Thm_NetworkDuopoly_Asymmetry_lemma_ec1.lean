-- Prove2me | Theorems.Thm_NetworkDuopoly_Asymmetry_lemma_ec1
-- name    : NetworkDuopoly.Asymmetry.lemma_ec1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:11.884667+00:00
-- url     : https://prove2.me/theorems/7cf75fb3-22fe-42d7-8d70-77994f429ed3
-- title:
--   Lemma EC.1 — properties of h, its inverse and the stationary-response curve
-- statement:
--   Let $\alpha\in\mathbb R$ and $\gamma>0$. Write $h(t)=t+\log t$ for $t>0$, $H(s)=W(e^s)$, $\bar y(x)=1-x-x/H(\alpha-1+\gamma x)$, and $c=(3-\sqrt5)/4$. Best responses refer to the global maximizers of the normalized revenue over $[0,1]$. The following five assertions hold.
--
--   1. $H(s)>0$ and $h(H(s))=s$ for every real $s$, and $H(h(t))=t$ for $t>0$. Both maps are strictly increasing on their domains, with
--   $$h'(t)=1/t+1,\qquad H'(s)=H(s)/(1+H(s)).$$
--   Moreover, $H(s)>s$ for $s<1$, and $H(s)<s$ for $s>1$.
--   2. The function $x\mapsto h(x/(1-2x))$ is concave on $(0,c)$ and convex on $(c,1/2)$.
--   3. $\bar y(0)=1$. A global best response to zero exists, and every such best response $y$ satisfies $y<1$.
--   4. For every $x\ge0$,
--   $$\bar y'(x)=-1-\frac{1-\gamma x/(H(\alpha-1+\gamma x)+1)}{H(\alpha-1+\gamma x)}.$$
--   Each of the three comparisons $\bar y'(x)<-1$, $\bar y'(x)=-1$, and $\bar y'(x)>-1$ is equivalent to the corresponding comparison of $x$ with $(e^\alpha+1)/\gamma$.
--   5. The derivative $\bar y'$ is strictly increasing on $[0,(e^\alpha+1)/\gamma)$. The second derivative exists at every $x\ge0$, and
--   $$\exists!\,x\ge0:\quad \bar y''(x)=0.$$
--
--   These analytic properties concern the stationary curve and its relationship to global response at zero; they do not identify every stationary point with a best response.
--
--   **Formalization Note** Positive $\gamma$ makes explicit the domain implicit in the printed quotient threshold. At $\gamma=0$, the unique-inflection assertion fails (finding F3); the goal uses positive strengths. The paper's increasing maps are encoded as strictly increasing, as established by its positive derivatives. Inverse identities unpack the source's term “inverse.” Existence and the bound for every maximizer make the notation $y^*(0)$ precise without choosing among ties. Explicit differentiability excludes default values of the total derivative operation. All five source clauses are retained together.
-- source:
--   Chen and Chen (2021), Duopoly Competition with Network Effects in Discrete Choice Models, https://doi.org/10.1287/opre.2020.2079; supplied artifact p. ec3 (PDF 47), Lemma EC.1, all five parts; proof pp. ec3–ec4 (PDF 47–48).

import Definitions.Def_NetworkDuopoly_Asymmetry_bestResponse
import Definitions.Def_NetworkDuopoly_Asymmetry_stationaryCurve

namespace NetworkDuopoly.Asymmetry

/- Imported declaration bodies (verbatim), included for standalone audit.
namespace AdvanceSales.Pricing
noncomputable def lambertW (a : ℝ) : ℝ :=
  by classical exact if h : ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = a then Classical.choose h else 0
end AdvanceSales.Pricing

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

noncomputable def h (t : ℝ) : ℝ := t + Real.log t

noncomputable def H (t : ℝ) : ℝ := AdvanceSales.Pricing.lambertW (Real.exp t)

noncomputable def stationaryCurve (α γ x : ℝ) : ℝ :=
  1 - x - x / H (α - 1 + γ * x)
-/

theorem lemma_ec1 (α γ : ℝ) (hγ : 0 < γ) :
    ((∀ t : ℝ, 0 < H t) ∧
      (∀ t : ℝ, h (H t) = t) ∧
      (∀ t : ℝ, 0 < t → H (h t) = t) ∧
      StrictMonoOn h (Set.Ioi 0) ∧ StrictMono H ∧
      (∀ t : ℝ, 0 < t → HasDerivAt h (1 / t + 1) t) ∧
      (∀ t : ℝ, HasDerivAt H (H t / (1 + H t)) t) ∧
      (∀ t : ℝ, t < 1 → t < H t) ∧
      (∀ t : ℝ, 1 < t → H t < t)) ∧
    (ConcaveOn ℝ (Set.Ioo 0 ((3 - Real.sqrt 5) / 4))
        (fun x : ℝ => h (x / (1 - 2 * x))) ∧
      ConvexOn ℝ (Set.Ioo ((3 - Real.sqrt 5) / 4) (1 / 2))
        (fun x : ℝ => h (x / (1 - 2 * x)))) ∧
    (stationaryCurve α γ 0 = 1 ∧
      (bestResponse α γ 0).Nonempty ∧
      ∀ y ∈ bestResponse α γ 0, y < 1) ∧
    ((∀ x : ℝ, 0 ≤ x →
        HasDerivAt (stationaryCurve α γ)
          (-1 - (1 - γ * x / (H (α - 1 + γ * x) + 1)) /
            H (α - 1 + γ * x)) x) ∧
      ∀ x : ℝ, 0 ≤ x →
        (deriv (stationaryCurve α γ) x < -1 ↔ x < (Real.exp α + 1) / γ) ∧
        (deriv (stationaryCurve α γ) x = -1 ↔ x = (Real.exp α + 1) / γ) ∧
        (-1 < deriv (stationaryCurve α γ) x ↔ (Real.exp α + 1) / γ < x)) ∧
    (StrictMonoOn (deriv (stationaryCurve α γ))
        (Set.Ico 0 ((Real.exp α + 1) / γ)) ∧
      (∀ x : ℝ, 0 ≤ x → DifferentiableAt ℝ (deriv (stationaryCurve α γ)) x) ∧
      ∃! x : ℝ, 0 ≤ x ∧ deriv (deriv (stationaryCurve α γ)) x = 0) := by sorry

end NetworkDuopoly.Asymmetry
