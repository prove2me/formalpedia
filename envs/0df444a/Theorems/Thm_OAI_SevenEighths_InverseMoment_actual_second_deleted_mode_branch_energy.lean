-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_second_deleted_mode_branch_energy
-- name    : OAI.SevenEighths.InverseMoment.actual_second_deleted_mode_branch_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:41.250982+00:00
-- url     : https://prove2.me/theorems/4b9e924d-24e6-4beb-bbe9-442a9efcffe7
-- title:
--   Cauchy-Schwarz bound for deleted second mode branches
-- statement:
--   Let $p$ be a family of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda`, with `goodLambda`$^2\mid p_i-1$ and residue characteristic $\ne2$; $u,v$ units; `source` a finite set of `MarkedSecondSource ι Jo 0` with `ActualSecondSourceConditions`; `pool`, $\Psi$ bounded by 1, $m$, a ray index $z$; slot sets `slots₁`, `slots₂`, $J_1,J_2$ with lists and coefficients ($a_k$ bounded by 1 on $J_k$); deleted sets inside the cube support, the first common part or dividing the quotient; $\omega_1,\omega_2$; reals $G,E,V,B,X,R$; a frequency $t$; `labels` containing every child label (`actualSecondChild p u v`); second frequencies in `nonzeroChildFrequencyBall (actualSecondMultiplier p x) R`; $K$ with $J_o\le2K$, $|J_1|,|J_2|\le K$; and weights $w$ bounded by 1. Then
--   $$\Big\|\sum_{x}\texttt{actualSecondSignedWeight}(\dots,x)\,w(x)\,\texttt{secondModeBranch}(\dots,x,u,v,\dots)\Big\|\le\sqrt{\sum_\gamma\texttt{tripleDivisorWeight}\,K\,\gamma\cdot E_{\mathrm{right}}(\gamma)}\cdot\sqrt{\sum_\gamma\texttt{tripleDivisorWeight}\,K\,\gamma\cdot E_{\mathrm{left}}(\gamma)},$$
--   $\gamma$ over `actualSecondTriples p u v` of the `varyingAssignedSource`, and $E_{\mathrm{right}},E_{\mathrm{left}}$ the `secondLabelEnergy` (squarefree labels, `nonzeroChildFrequencyBall 1 R`) of `secondModeRight` (slots $\mathrm{slots}_2\setminus J_2$, $\omega_2$) and `secondModeLeft` (slots $\mathrm{slots}_1\setminus J_1$, $\omega_1$).
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_second_deleted_mode_branch_energy` in `lean/OAI/NumberTheory/DirichletL/Descent/SecondDeletedModeEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
