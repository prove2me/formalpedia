-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstPhysicalSource_block_eq_whole
-- name    : OAI.SevenEighths.CenteredMomentFirstPhysicalSource.block_eq_whole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:24:58.975957+00:00
-- url     : https://prove2.me/theorems/516a5242-5b4c-4a52-9aaf-ac48db8ed58d
-- title:
--   A physical block written with the whole kernel
-- statement:
--   Let $\eta$ be a `Character`, $m,A$ Eisenstein integers, $t$ real, $S$ finite ideals with coefficients $c$, `Supported` ideals $C,D$ with the same prime support, $E\subseteq$`CommonIndex C D`, nonzero `rows`, $W$ Schwartz, $V:\mathrm{Fin}\,4\to\mathbb R\to\mathbb C$, and $K,K_0,H_0,A_0,B_0>0$. With $e=$`primeSubsetGenerator E`, $k=K/\|\texttt{eisEmbedding}\,e\|^2$, $r=$`activeConductor C D` and $\rho=$`finiteSexticRow …`, `block η m A t S c C D … E rows W V K K₀ H₀ A₀ B₀` equals `scalar C D hC E K A₀ B₀` times
--   $$\sum_{h\in\mathrm{rows}}\overline{\rho(h)}\sum_{a}\sum_{b}[x_a,y_b\text{ coprime}]\,\texttt{originalPhase}\,e\,r\,\rho\,x_a\,y_b\cdot c_\eta(C,a)\overline{c_\eta(D,b)}\cdot\texttt{gaussRow}(x_a,h)\overline{\texttt{gaussRow}(y_b,-h)}\cdot\texttt{wholeKernel}\,W\,V\,\frac{K_0H_0}{A_0B_0}\,(\dots),$$
--   where $x_a,y_b$ are the column elements, $c_\eta$ the `coefficient η m A t c`, and the four kernel arguments are the logarithms $\log((k/\|r\|^2)/K_0)$, $\log(\|h\|^2/H_0)$, $\log(\|x_a\|^2/A_0)$, $\log(\|y_b\|^2/B_0)$ of norms of `eisEmbedding`s.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstPhysicalSource.block_eq_whole` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSource.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem block_eq_whole (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0<K)(hK₀:0<K₀)(hH₀:0<H₀)(hA₀:0<A₀)(hB₀:0<B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖eisEmbedding r‖^2)/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
            (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)):= by
  sorry

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end
