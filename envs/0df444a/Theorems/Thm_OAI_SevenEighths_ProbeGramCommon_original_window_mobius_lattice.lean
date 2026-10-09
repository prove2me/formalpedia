-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_original_window_mobius_lattice
-- name    : OAI.SevenEighths.ProbeGramCommon.original_window_mobius_lattice
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:44:02.77002+00:00
-- url     : https://prove2.me/theorems/41c85c60-b15c-480e-86ce-8eadbe83dcf5
-- title:
--   Coprime column pairs expanded by Möbius inversion
-- statement:
--   For a finite set $S$ of maximal ideals containing `fixedBadPrimes`, $\sigma$, $C\equiv1\bmod\lambda_0^2$, $k$, $u,a,b$, a `Supported` $r$, maximal ideals $P_i$ avoiding $\lambda_0$ with exponents $c_i$, compactly supported $W$, $N>0$, Schwartz $U$ and reals $v,T$: the sum over pairs of coprime low Gauss columns $I,J$ of `jointExtension …(I_gen)(J_gen)`·`shellProfile W v U T (N(I)/N) (N(J)/N)` equals
--   $$\sum_{D}\mu(D)\sum_{n,m\in\mathcal O}\texttt{jointExtension}(\dots,D_{\mathrm{gen}}n,D_{\mathrm{gen}}m)\,\texttt{shellProfile}\,W\,v\,U\,T\Big(\frac{\|n\|^2}{N/N(D)}\Big)\Big(\frac{\|m\|^2}{N/N(D)}\Big),$$
--   $D$ over the divisor pool of the columns and $\|\cdot\|$ the norm of `eisEmbedding`.
--
--   Lean: `OAI.SevenEighths.ProbeGramCommon.original_window_mobius_lattice` in `lean/OAI/NumberTheory/DirichletL/Detector/GramWindowMobius.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
            shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
              (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  sorry

end SevenEighths.ProbeGramCommon
end

end OAI
end
