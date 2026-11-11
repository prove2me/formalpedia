-- Prove2me | Theorems.Thm_HigherOrderId_Certify_lemma_B_2
-- name    : HigherOrderId.Certify.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:24.642984+00:00
-- url     : https://prove2.me/theorems/6a00d659-432b-4a3b-8bc0-6ea52c83f4dc
-- title:
--   Lemma B.2 — rank threshold: Q ↦ QV_env is injective on S^d_0 iff D_U is; never when (m+1 choose 2) > d; always for m = 0 and for the frame (64)
-- statement:
--   Let $d\ge10$ and let $[U,V_{\mathrm{env}}]$ be a $d\times d$ orthogonal matrix, $U$ with $m$ columns and $V_{\mathrm{env}}$ with $k=d-m$ columns, so that $\mathrm{Col}(U)=\mathcal V^\perp$ for the span $\mathcal V=\mathrm{Col}(V_{\mathrm{env}})$ of a centered design. Then:
--
--   1. the noiseless gradient channel $Q\mapsto QV_{\mathrm{env}}$ is injective on $S^d_0$ if and only if $D_U(B)=\operatorname{diag}(UBU^\top)$ is injective on $\mathrm{Sym}_m$;
--   2. if $\binom{m+1}{2}>d$, the channel is not injective (no such centered design is identifying);
--   3. if $m=0$ the channel is injective;
--   4. if $m\ge1$, $\binom{m+1}2\le d$ and $U=U_w$ is the frame (64) for some $1\le w\le m$, the channel is injective.
--
--   The lemma locates the algebraic identification threshold $m\le m_d$ of the centered class.
--
--   Differences from the source:
--   - encoding: a centered design spanning V = Col(V_env), with Col(U) = V^⊥ → matrices U (d × m), V (d × k) with m + k = d, UᵀU = I, VᵀV = I, UᵀV = 0; reason: these say exactly that [U, V_env] is orthogonal; the channel Q ↦ QV_env depends on the design only through V_env
--   - encoding: "no centered design with (m+1 choose 2) > d is identifying" → for every such [U, V], some Q ∈ S^d_0 with Q ≠ 0 has QV = 0; reason: identifying means the channel is injective on S^d_0
--   - reading: "the frame (64) below is identifying whenever (m+1 choose 2) ≤ d" → for every 1 ≤ w ≤ m and every V completing U = U_w to an orthogonal matrix; reason: (64) is defined for every 1 ≤ w ≤ m, and V_env is any orthonormal basis of Col(U)^⊥
--   - generalization: G_w lists the rows √w e_iᵀ, then (e_i + e_j)ᵀ (i < j), then d − t zero rows → the t nonzero rows are placed in any rows given by an injection ι of the frame-row index set into Fin d (which exists iff (m+1 choose 2) ≤ d), all other rows zero; reason: a row permutation of U is an orthogonal change of coordinates of ℝ^d and does not change injectivity of D_U or of the channel; the paper's order is one choice of ι
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 21, Lemma B.2 (PDF p. 22)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

open Matrix

namespace HigherOrderId.Certify

/-- Lemma B.2 (rank threshold inside the centered class). Let `[U, V]` be a `d × d` orthogonal
matrix with `U` of size `d × m` (so `Col(U) = V^⊥`, `V = Col(V_env)`). The noiseless gradient
channel `Q ↦ Q V_env` is injective on `S^d_0` exactly when `D_U` is injective on `Sym_m`; it is
never injective when `(m+1 choose 2) > d`; it is injective when `m = 0`; and for `m ≥ 1` it is
injective for the frame `U = U_w` of (64) (any `1 ≤ w ≤ m`; the frame's `t = (m+1 choose 2)`
nonzero rows fit in `d` rows, i.e. `(m+1 choose 2) ≤ d`). -/
theorem lemma_B_2 (d m k : ℕ) (hd : 10 ≤ d) (hmk : m + k = d)
    (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hUV : Uᵀ * V = 0) :
    ((∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) ↔
        FullColRank U) ∧
    (d < (m + 1).choose 2 →
        ∃ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q ∧ Q ≠ 0 ∧ Q * V = 0) ∧
    (m = 0 → ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) ∧
    (∀ (ι : FrameRows m ↪ Fin d) (w : ℝ), 1 ≤ m → 1 ≤ w → w ≤ (m : ℝ) → U = Uw ι w →
        ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Q * V = 0 → Q = 0) := by sorry

end HigherOrderId.Certify
