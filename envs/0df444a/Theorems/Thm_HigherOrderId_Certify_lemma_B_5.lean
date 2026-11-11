-- Prove2me | Theorems.Thm_HigherOrderId_Certify_lemma_B_5
-- name    : HigherOrderId.Certify.lemma_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:18:55.422023+00:00
-- url     : https://prove2.me/theorems/3088d93f-8a8d-4561-a660-c779ae0557eb
-- title:
--   Lemma B.5 — tall completion identity MM* = (D_U*D_U)^{-1} − I_t, the spectrum of L, unbiasedness, and the trace bounds (74)–(75)
-- statement:
--   Let $d\ge10$, let $[U,V_{\mathrm{env}}]$ be orthogonal with $U$ of size $d\times m$, and suppose $D_U$ has full column rank with singular values $a_1,\dots,a_t$. Put $M=D_U^\dagger D_{\mathrm{rest}}$ and $L(r)=r-U\{M(r)\}U^\top$ for $r\in R_{U,V_{\mathrm{env}}}$. Then
--   $$MM^*=(D_U^*D_U)^{-1}-I_t,\tag{73}$$
--   and, counting multiplicity, the squared spectrum of $L$ consists of $a_1^{-2},\dots,a_t^{-2}$ together with $\dim R_{U,V_{\mathrm{env}}}-t$ ones. The linear completion $\widehat Q$ obtained from (55) (retain $U^\top\widehat M_g$ and $\operatorname{sym}(V_{\mathrm{env}}^\top\widehat M_g)$, apply $L$, project onto $S^d_0$) is unbiased for every $Q\in S^d_0$, and its noise covariance $\Gamma_{U,V_{\mathrm{env}}}$ on $S^d_0$ satisfies
--   $$\operatorname{tr}\Gamma_{U,V_{\mathrm{env}}}\le2v_N\Big(\dim R_{U,V_{\mathrm{env}}}-t+\sum_{j=1}^ta_j^{-2}\Big),\qquad \operatorname{tr}\Gamma_{U,V_{\mathrm{env}}}^2\le4v_N^2\Big(\dim R_{U,V_{\mathrm{env}}}-t+\sum_{j=1}^ta_j^{-4}\Big).$$
--
--   This converts the inverse spectrum of $D_U$ into the integrated and Frobenius-norm size of the completion estimator's covariance.
--
--   Differences from the source:
--   - encoding: Q̂ is unbiased for every Q ∈ S^d_0 → Q̂ applied to the noiseless observation QV_env returns Q; reason: Q̂ is linear in M̂_g = QV_env + √v_N Z and E Z = 0, so E Q̂ = Q̂(QV_env)
--   - encoding: Γ_{U,V_env}, the noise covariance of Q̂ as an operator on S^d_0 → v_N K Kᵀ, the covariance of the entries of Q̂ (K the matrix of M̂_g ↦ Q̂); reason: Z has independent standard normal entries; the operator vanishes off S^d_0, so its trace and the trace of its square equal those on S^d_0
--   - encoding: v_N = σ²k/(Nα²) → any v_N > 0; reason: the lemma concerns the channel (55) at noise level v_N, and σ²k/(Nα²) takes every positive value
--   - encoding: M M*, L*L, dim R_{U,V_env}, D_U^† → matrices in orthonormal bases of Sym_m and R_{U,V_env}; card of the basis index; (D_U*D_U)⁻¹D_U*; reason: coordinate forms of the same operators; D_U^† is the Moore–Penrose inverse, which equals this under full column rank
--   - encoding: "counting multiplicity, L has squared spectrum {a_j^{-2}} plus ones" → the multiset of eigenvalues of L*L equals {a_j^{-2}} + (dim R − t)·{1}; reason: multiset form of 'counting multiplicity'
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), pp. 24–25, Lemma B.5 (PDF pp. 25–26)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion

open Matrix

namespace HigherOrderId.Certify

/-- Lemma B.5 (tall completion identity). Let `[U, V]` be orthogonal (`U` is `d × m`, `V` is
`d × k`) and let `D_U` have full column rank with singular values `a_1, …, a_t`. Then
`M M* = (D_U* D_U)⁻¹ − I_t` (73); the squared singular values of `L` are the `a_j^{-2}` together
with `dim R_{U,V} − t` ones; the linear completion `Q̂` is unbiased for every `Q ∈ S^d_0`; and its
noise covariance `Γ_{U,V}` under the channel (55) with noise level `v_N > 0` satisfies (74)
and (75). -/
theorem lemma_B_5 (d m k : ℕ) (hd : 10 ≤ d) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) (hfull : FullColRank U)
    (v : ℝ) (hv : 0 < v) :
    MMadj U V = ((DUmat U)ᴴ * DUmat U)⁻¹ - 1 ∧
    Multiset.map (LsqSpec U V) Finset.univ.val =
      Multiset.map (fun j => (singVals U j)⁻¹ ^ 2) Finset.univ.val +
        Multiset.replicate (Fintype.card (RestIdx m k) - Fintype.card (SymIdx m)) 1 ∧
    (∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Qhat U V (Q * V) = Q) ∧
    (GammaEntry U V v).trace ≤
      2 * v * ((Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
        ∑ j, (singVals U j)⁻¹ ^ 2) ∧
    (GammaEntry U V v * GammaEntry U V v).trace ≤
      4 * v ^ 2 * ((Fintype.card (RestIdx m k) : ℝ) - Fintype.card (SymIdx m) +
        ∑ j, (singVals U j)⁻¹ ^ 4) := by sorry

end HigherOrderId.Certify
