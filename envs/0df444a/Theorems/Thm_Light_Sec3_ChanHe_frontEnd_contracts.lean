-- Prove2me | Theorems.Thm_Light_Sec3_ChanHe_frontEnd_contracts
-- name    : Light.Sec3.ChanHe.frontEnd_contracts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T17:21:21.232826+00:00
-- url     : https://prove2.me/theorems/103193a7-1763-4155-9607-553d4acec08e
-- title:
--   Verified front-end contracts for the Chan–He 3SUM reduction
-- statement:
--   The deterministic Chan–He 3SUM reduction’s front-end procedures satisfy their exact light-language contracts for correctness, running time, memory layout, and resource use. This bundles the 15 source lemmas for remainder computation, logarithms, prime enumeration, sorting, distinctness, binary decomposition, remainders and counts, collision and heavy-element handling, modulus selection, node arrays, parameter construction, and preparation. The separate host proof combines these verified routines into the complete reduction.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Program.lean#L124-L149

import Definitions.Def_ThreeSumSource_CH20Contracts
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem Light.Sec3.ChanHe.frontEnd_contracts :
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.emodBody → Light.Sec3.ChanHe.EmodSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.clog2Body → Light.Sec3.ChanHe.Clog2Spec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.log2Body → Light.Sec3.ChanHe.Log2Spec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.sieveBody → Light.Sec3.ChanHe.PrimesSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pHalf pMerge pCopy : ℕ},
  Light.MergeSort.Procs P p pHalf pMerge pCopy → Light.Sec3.ChanHe.SortSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.distinctBody → Light.Sec3.ChanHe.DistinctSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.bitsBody → Light.Sec3.ChanHe.BitsSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pEmod : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.residBody pEmod) →
    Light.Sec3.ChanHe.EmodSpec lim P pEmod → Light.Sec3.ChanHe.ResidSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.tallyBody → Light.Sec3.ChanHe.TallySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.collBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.CollSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.heavyBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.HeavySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {pSearch pColl p : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.modulusBody pSearch pColl) →
    P[pSearch]? = some (Light.Sec3.ChanHe.searchBody pColl) →
      Light.Sec3.ChanHe.CollSpec lim P pColl → Light.Sec3.ChanHe.ModulusSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.nodeArrayBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.NodeArraySpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pLog2 pClog2 pSqrt : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.paramsBody pLog2 pClog2 pSqrt) →
    Light.Sec3.ChanHe.Log2Spec lim P pLog2 →
      Light.Sec3.ChanHe.Clog2Spec lim P pClog2 → P[pSqrt]? = some Light.sqrtBody → Light.Sec3.ChanHe.ParamsSpec lim P p) ∧
(∀ {lim : Light.Limits} {P : Light.Program} {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.prepBody pPrimes pFill pCopy pSort pDistinct pBits) →
    Light.Sec3.ChanHe.PrimesSpec lim P pPrimes →
      P[pFill]? = some Light.fillBody →
        P[pCopy]? = some Light.copyBody →
          Light.Sec3.ChanHe.SortSpec lim P pSort →
            Light.Sec3.ChanHe.DistinctSpec lim P pDistinct →
              Light.Sec3.ChanHe.BitsSpec lim P pBits → Light.Sec3.ChanHe.PrepSpec lim P p) := by sorry
