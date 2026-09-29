-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates
-- name    : ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/d09a7a57-1356-5b48-bc7f-6947c07aaf73
-- title:
--   Unimodular recombination of the good family carrying wide-node certificates
-- statement:
--   Let $p$ be a prime with $13 \le p$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a nonunit (`A.LiesOverPrime p`), with residue field $k$ of characteristic $p$, let $\Gamma$ be a chart context for $p$ and $A$ — supplying the two component charts `infChart` $\Gamma$ and `zeroChart` $\Gamma$ of the field $\overline{\mathbb Q}$-field $\overline{F} =$ `modularFunctionFieldBar (1 * p)` over $A$ with residue field the level-one field `modularFunctionFieldC k 1`, the supersingular values $a_e =$ `ssValue` $\Gamma\,e$ for $e$ in `Fin (mAnnuli p)`, and the node places `nodeSrc` $\Gamma\,e$, `nodeTgt` $\Gamma\,e$ of `modularFunctionFieldC k 1` at $a_e^p$ and at $a_e$ — and let $\Delta$ be an annulus context for $\Gamma$. Let $r$ be a natural number and $\Phi$ a family context of rank $r$ (an embedding basis $t_0 = 1, t_1,\dots,t_{r-1}$ of $\overline F$ with rational Laurent representatives, together with the prescribed reductions on the two charts), write $n_l =$ `hasseExp` $\Phi\,l$ for the $p$-adic content exponents and $w_e =$ `jWidth` $a_e$ (equal to $3$ if $a_e = 0$, to $2$ if $a_e = 1728$, and to $1$ otherwise). Assume the rescaled members `goodFamilyZero` $\Phi\,l = p^{-n_l} t_l$ all lie in the integers of `zeroChart` $\Gamma$ and that their residues are linearly independent over $k$. Then there are a matrix $U$ over $\mathbb Q$ of size $r$, a family datum $D'$ of rank $r$, and integrality witnesses for `goodFamilyZero` $D'\,l$ on `zeroChart` $\Gamma$ and for $D'.t\,l$ on `infChart` $\Gamma$, such that: $U$ is invertible; each entry of $U$ and of $U^{-1}$ either vanishes or has $p$-adic valuation at least $\max(0, n_i - n_j)$; the zeroth row of $U$ is the first standard basis vector; $D'.tRat\,i = \sum_j U_{ij}\,\Phi.tRat\,j$ and correspondingly $D'.t\,i = \sum_j U_{ij} t_j$ in $\overline F$; `hasseExp` $D' = n$, with `goodFamilyZero` $D'\,l = p^{-n_l}\sum_j U_{lj} t_j$; the residues of `goodFamilyZero` $D'$ on `zeroChart` $\Gamma$ remain linearly independent over $k$; some $l \ge 1$ has $n_l = 1$; if some node has $w_e \ne 1$ then some $l$ has $n_l = 2$; every residue of $D'.t\,l$ on `infChart` $\Gamma$ is nonzero; for all $e$ and $l$ the order of the `zeroChart` residue of `goodFamilyZero` $D'\,l$ at `nodeSrc` $\Gamma\,e$ is $-\lfloor n_l/w_e\rfloor$; for $l \ge 1$ the order of the `infChart` residue of $D'.t\,l$ at `nodeTgt` $\Gamma\,e$ is $1$ whenever $w_e \ne 1$ and also whenever $n_l = 1$, and is $2$ whenever $n_l = 2$ and $w_e = 1$; for $l \ge 1$ with $n_l = 1$ and distinct nodes $e \ne e'$ with $w_e \ne 1 \ne w_{e'}$, the values `evalAt` of the `zeroChart` residue of `goodFamilyZero` $D'\,l$ at `nodeSrc` $\Gamma\,e$ and at `nodeSrc` $\Gamma\,e'$ differ; and for $l \ge 1$ with $n_l = 1$ and $w_e = 3$ there is $c \in k$ with the order of that residue minus $c$ at `nodeSrc` $\Gamma\,e$ equal to $1$.
--
--   This is the recombination step in the construction of a certified family of functions on the two-component semistable covering attached to $X_0(p)$: a single invertible rational change of basis, bi-filtered by the $p$-adic contents and fixing the constant member, is produced which simultaneously realises all the node certificates (prescribed orders at the node places of both charts, separation of wide nodes, and a simple zero near a node of width $3$). It is used by the cross-comparison lemmas for annuli and for the zero chart, and through them by the existence theorem for a uniform multiplicative covering with a certified family at primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers),
      IsUnit U ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
        ∨ U i j = 0) ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
        ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ hasseExp Φ.toFamData l = 1) ∧
      ((∃ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≠ 1) → ∃ l : Fin r, hasseExp Φ.toFamData l = 2) ∧
      (∀ l, (infChart Γ).residue ⟨D'.t l, hintI' l⟩ ≠ 0) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r),
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)
          = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ)) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → jWidth (ssValue Γ e) ≠ 1 →
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 1) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 →
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 1) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 → jWidth (ssValue Γ e) = 1 →
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l, hintI' l⟩) = 2) ∧
      (∀ (e e' : Fin (mAnnuli p)) (l : Fin r), e ≠ e' → jWidth (ssValue Γ e) ≠ 1 → jWidth (ssValue Γ e') ≠ 1 →
        1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 →
        (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)
          ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)) ∧
      (∀ (e : Fin (mAnnuli p)) (l : Fin r), jWidth (ssValue Γ e) = 3 → 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 →
        ∃ c : ResidueField ↥A,
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩
            - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1) := by sorry
