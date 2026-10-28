-- Prove2me | Theorems.Thm_LambdaVaRAmb_Robust_proposition_5_properties
-- name    : LambdaVaRAmb.Robust.proposition_5_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:40.678978+00:00
-- url     : https://prove2.me/theorems/0b519aa7-817a-4335-9643-717a3886e66b
-- title:
--   Proposition 5 (Moreover) — for finite strictly convex superlinear φ, g_{φ,δ} increases continuously up to x_δ, equals 1 after, and g_{φ,δ}(x) ↓ x as δ ↓ 0
-- statement:
--   Let $\phi:[0,\infty)\to\mathbb R$ be convex and finite, with $\phi(1)=0$ and $\phi(0)=\lim_{x\downarrow0}\phi(x)$, and assume moreover that $\phi$ is strictly convex and $\lim_{x\to\infty}\phi(x)/x=\infty$. Let $g_{\phi,\delta}$ be the distortion of Proposition 5: $g_{\phi,\delta}(0)=0$, $g_{\phi,\delta}(1)=1$, and $g_{\phi,\delta}(x)=\sup\{t\in[x,1]: x\phi(t/x)+(1-x)\phi((1-t)/(1-x))\le\delta\}$ for $x\in(0,1)$. Then:
--
--   1. for every $\delta>0$ the equation
--   $$x\phi(1/x)+(1-x)\phi(0)=\delta$$
--   has exactly one solution $x_\delta\in(0,1)$; $g_{\phi,\delta}$ is continuous and strictly increasing on $[0,x_\delta]$, and $g_{\phi,\delta}(x)=1$ for $x\in[x_\delta,1]$;
--   2. for every $x\in(0,1)$: $g_{\phi,\delta}(x)>x$ for all $\delta>0$, $\delta\mapsto g_{\phi,\delta}(x)$ is nondecreasing on $(0,\infty)$, and $g_{\phi,\delta}(x)\to x$ as $\delta\downarrow0$.
--
--   These properties make $g_{\phi,\delta}$ invertible on $(0,1)$, which is what turns the robust $\Lambda$VaR into $(g^{-1}_{\phi,\delta}\circ\Lambda)$VaR under $\mathbb P$ in Theorem 2, and they give the limit $\delta\downarrow0$ there.
--
--   **Formalization Note** "$\phi:[0,\infty)\to\mathbb R$" is the hypothesis that $\phi$ is finite on $[0,\infty)$; strict convexity and superlinearity are stated for the real function $x\mapsto\phi(x)$ on $[0,\infty)$. "$x_\delta$ being the solution" is posed as existence and uniqueness in $(0,1)$. "$g_{\phi,\delta}(x)\downarrow x$ as $\delta\downarrow0$" is posed as monotonicity in $\delta$ together with the limit along $\delta\to0^+$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, pp. 11–12, Proposition 5 ("Moreover" part); proof pp. 32–33

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Robust

open Filter Topology

theorem proposition_5_properties (φ : ℝ → EReal) (hφ : IsPhiFunction φ)
    (hfin : ∀ x : ℝ, 0 ≤ x → φ x ≠ ⊤)
    (hsc : StrictConvexOn ℝ (Set.Ici 0) (fun x => (φ x).toReal))
    (hsl : Tendsto (fun x => (φ x).toReal / x) atTop atTop) :
    (∀ δ : ℝ, 0 < δ → ∃ xδ ∈ Set.Ioo (0 : ℝ) 1,
        xδ * (φ (1 / xδ)).toReal + (1 - xδ) * (φ 0).toReal = δ ∧
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, x * (φ (1 / x)).toReal + (1 - x) * (φ 0).toReal = δ → x = xδ) ∧
        ContinuousOn (gPhi φ δ) (Set.Icc 0 xδ) ∧ StrictMonoOn (gPhi φ δ) (Set.Icc 0 xδ) ∧
        ∀ x ∈ Set.Icc xδ 1, gPhi φ δ x = 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1,
        (∀ δ : ℝ, 0 < δ → x < gPhi φ δ x) ∧
        MonotoneOn (fun δ => gPhi φ δ x) (Set.Ioi 0) ∧
        Tendsto (fun δ => gPhi φ δ x) (𝓝[>] 0) (𝓝 x)) := by sorry

end LambdaVaRAmb.Robust
