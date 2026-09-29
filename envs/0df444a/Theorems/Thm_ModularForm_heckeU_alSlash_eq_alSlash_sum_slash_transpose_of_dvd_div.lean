-- Prove2me | Theorems.Thm_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
-- name    : ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/95c3a468-9dd9-5647-9523-11cd95e9766a
-- title:
--   Atkin–Lehner conjugation turns U_{q'} into its transpose
-- statement:
--   Let $M$ be a non-zero natural number and $p$ a prime with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit that maps to $1$ under the reduction $\mathrm{ZMod.unitsMap}$ attached to $M/p \mid M$, i.e. containing the kernel of $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and let $W$ be an Atkin–Lehner datum for the pair $(M, M/p)$: data consisting of $R \in \mathbb{N}$ with $M = (M/p)R$ and integers $a, b$ with $(M/p)a - Rb = 1$, from which `ModularForm.alGL` produces the invertible real matrix obtained by mapping the associated integral matrix `W.mat`, of determinant $M/p$, into $GL_2(\mathbb{R})$, and [`ModularForm.alSlash W k`](def/ModularForm_AtkinLehnerDatum.html#L141) is the weight-$k$ slash action by that matrix. Let $q'$ be a prime dividing $M/p$, let $k \in \mathbb{Z}$, and let $f : \mathbb{H} \to \mathbb{C}$ satisfy $f \mid_k \gamma = f$ for every $\gamma$ in the image in $GL_2(\mathbb{R})$ of [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $SL_2(\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H$ modulo $M$. Then $$\sum_{j=0}^{q'-1} \bigl(f \mid_k W\bigr) \Bigm|_k \begin{pmatrix} 1 & j \\ 0 & q'\end{pmatrix} \;=\; \Bigl( \sum_{j=0}^{q'-1} f \mid_k \begin{pmatrix} q' & 0 \\ 0 & 1\end{pmatrix} S T^{-Mj} S^{-1} \Bigr) \Bigm|_k W,$$ where the left-hand side is [`ModularForm.heckeU k q'`](def/ModularForm_HeckeOperator.html#L93) applied to $f \mid_k W$, the upper triangular matrices are [`ModularForm.heckeMatrix q' j`](def/ModularForm_HeckeOperator.html#L18), the diagonal one is [`ModularForm.heckeDiagMatrix q'`](def/ModularForm_HeckeOperator.html#L21), and $S T^{-Mj} S^{-1}$ is the image in $GL_2(\mathbb{R})$ of the indicated product of the standard generators of $SL_2(\mathbb{Z})$, so that the slashing matrix is $\begin{pmatrix} q' & 0 \\ Mj & 1\end{pmatrix}$.
--
--   This is the Atkin–Lehner relation $w_Q U_{q'} w_Q^{-1} = U_{q'}^{t}$ for a prime $q'$ dividing $Q = M/p$, with the transposed operator written as slashing by the lower triangular matrices $\begin{pmatrix} q' & 0 \\ Mj & 1\end{pmatrix}$; plain commutation of $U_{q'}$ with $w_Q$ fails in this range. It is used downstream in the study of the $U_{q'}$-operator on integral cusp forms and in matching $U_{q'}$ with a Hecke correspondence on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (q' : ℕ) (hq' : q'.Prime) (hq'Q : q' ∣ M / p) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k q' (ModularForm.alSlash W k f) =
      ModularForm.alSlash W k
        (∑ j ∈ Finset.range q',
          f ∣[k] (ModularForm.heckeDiagMatrix q' *
            (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-((M * j : ℕ) : ℤ)) * ModularGroup.S⁻¹) :
              GL (Fin 2) ℝ))) := by sorry
