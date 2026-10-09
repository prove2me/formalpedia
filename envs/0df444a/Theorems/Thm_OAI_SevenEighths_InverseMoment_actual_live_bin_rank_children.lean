-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_live_bin_rank_children
-- name    : OAI.SevenEighths.InverseMoment.actual_live_bin_rank_children
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:00:06.310782+00:00
-- url     : https://prove2.me/theorems/1f45449a-0cc5-4530-aae9-167a1eab5bbb
-- title:
--   Child bounds for a live cube-log bin from rank moments
-- statement:
--   Let $S$ be a finite set of ideals of the Eisenstein integers containing `fixedBadPrimes`, $D\in\mathbb N$, and let $F=$`outsideSquarefreeIdeals S D` with its pool of primes `poolPrimary F`. Fix reals $Z>1$, $L\ge1$, $0\le\eta\le1$, `cutoff` $>0$ with $\eta\le\mathrm{cutoff}/32$, $V\ge0$ with $N+V\le L$, and the further numerical hypotheses of the Lean ($b_W\le Z^\eta$, $\eta\log Z\ge1$, $e\le Z^\eta$, $Z^\eta\ge2$, $1\le b\le Z^{6\eta}$, $e^{\mathrm{window}}\le Z^{4\eta}$, $M-\tfrac34\mathrm{cutoff}\le M_{\mathrm{next}}$, $N+V+15\eta\le F_{\mathrm{next}}$, $c_{\mathrm{next}}\le c-7\eta$), a bin index $j$ for which `progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)` is nonempty, a base ray twist $\Psi$ of `base` (`IsBaseRayTwist`), $m\ne0$ whose radical has norm $\le Z^{Q_{\mathrm{width}}}$, parent margins `CanonicalMargins (N+V) M Qwidth z c`, slot data and Schwartz $\omega_1,\omega_2$, $K$, `degree`. If `CanonicalRankMoments` holds (for the pool, `base`, the slots, at parameters $Z,M_{\mathrm{next}},F_{\mathrm{next}},z,c_{\mathrm{next}},\mathrm{eps},A,K,\mathrm{degree}$) both with $\omega_1$ and with $\omega_2$, then for every source index $k$, all $l,jj\in\mathbb N$ and every Boolean `negative`, `ChildBounds` holds for the progressing cubes of that bin with parameters $Z$, $M$, $N-3\ell_j$, $\ell_j$ (where $\ell_j=$`actualCubeLength Z j`), $V,\eta,\tau$, `window`, $b$, eps, $A$, $K$, `degree`.
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_live_bin_rank_children` in `lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLiveBinRank.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_bin_rank_children
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:0≤eta)(heta1:eta≤1)
    (hcut:0<cutoff)(hsmall:eta≤ cutoff/32)(hV:0≤V)(hparentcap:N+V≤L)
    (hbW:bW≤Z^eta)(hlog:1≤eta*Real.log Z)(hexp:Real.exp 1≤Z^eta)
    (hbin:2≤Z^eta)(hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤Mnext)(hFc:N+V+15*eta≤Fnext)(hcc:cnext≤ c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
