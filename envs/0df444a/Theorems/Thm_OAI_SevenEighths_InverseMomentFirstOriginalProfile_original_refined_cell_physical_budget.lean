-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMomentFirstOriginalProfile_original_refined_cell_physical_budget
-- name    : OAI.SevenEighths.InverseMomentFirstOriginalProfile.original_refined_cell_physical_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:56.394986+00:00
-- url     : https://prove2.me/theorems/f56446e3-732d-4e71-b78c-2d8aef8d4db8
-- title:
--   Refined cell rows bounded by refined child energies
-- statement:
--   Let $g_1,g_2,\Phi$ be Schwartz with $g_k$ supported in $[-m_k,m_k]$, $m_k\ge0$. Then there are compactly supported Schwartz $\omega_1,\omega_2$ with support in $[lo,hi]$, $0<lo\le hi$, such that for every $\varepsilon>0$ and $A_{\mathrm{ker}},J\in\mathbb N$ there are $C_{\mathrm{profile}}\ge0$, $K_{\mathrm{push}}>0$ with the following property. For every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` (residue characteristic $\ne2$, `goodLambda`$^2\mid p_i-1$), `pool`, $Q$, squarefree nonzero `labels`, coefficients $\beta$ bounded by $\Gamma\ge0$, a cutoff bounded by $Y>0$ on `refinedOuter p pool Q k gate`, $\Psi$ bounded by 1, $m$, `mark`, $Y_{\mathrm{source}}$, a source index $k$, $l$, a gate, reals $T_1,T_2,K>0$, $\theta$, $L=\eta\log Z\ge0$, $B_{\mathrm{energy}}\ge0$, $Z>0$ and $M,r,\ell,V,\delta,a_1,a_2,b,r',t_q,h$ with `rawScales k l T₁ T₂` $=(Z^{a_1},Z^{a_2},Z^b,Z^\delta,Z^{r'},Z^{t_q},Z^h,Z^{r-a_1-b-t_q},Z^{r-a_2-b-t_q})$: if the scaled left and right `refinedChildEnergy` values (with $\omega_1$ at $T_1$ and coordinate 7, with $\omega_2$ at $T_2$ and coordinate 8) are at most $B_{\mathrm{energy}}\cdot$`tripleHeight J`·`coordinateHeight J` for every frequency, then
--   $$Z^{-r-2\ell-V}Z^M\,\|\texttt{refinedCellRows}(\dots,\texttt{positiveSource}\,g_1\,1\,(-\theta),\texttt{positiveSource}\,g_2\,1\,\theta,\Phi,K,Y_{\mathrm{source}},s)\|\le\Gamma^2K_{\mathrm{push}}Y^{\varepsilon}B_{\mathrm{energy}}\cdot\frac{C_{\mathrm{profile}}(1+|\theta|)^{2k}}{(1+Ks_6/(s_3s_4s_5^2T_1T_2))^{A_{\mathrm{ker}}}},$$
--   $s=$`rawScales k l T₁ T₂`, $k=$`momentOrder J`.
--
--   Lean: `OAI.SevenEighths.InverseMomentFirstOriginalProfile.original_refined_cell_physical_budget` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstOriginalProfileLiveEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem original_refined_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Ysource Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop)
      (_hcutoff : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Y)
      (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Ysource (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  sorry

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end
