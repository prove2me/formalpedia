-- Prove2me | Theorems.Thm_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily
-- name    : ModularCurve.annulusComparison_of_attached_at_both_ends_of_adaptedFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/ab6f2d42-57c4-5aac-8532-7f2e91148aed
-- title:
--   Uniform proximity–parameter comparison on a doubly attached annulus
-- statement:
--   Let $N\ge 1$, let $s:\mathrm{Fin}\,r\to$ `modularFunctionFieldBar N` be a family that is linearly independent over $\bar{\mathbb Q}$ and spans the Riemann–Roch space of `embDivisor N`, and let $p$ be a prime with $p\mid N$ and $p^2\nmid N$. Then for every $k_0$, every family $t$ with $t_0=1$, matrices $M,M^{-1}$ over $\bar{\mathbb Q}$ inverse to each other on both sides with $s_i=\sum_j M_{ij}t_j$, and exponents $\mathrm{nexp}$ with $\mathrm{nexp}_0=0$, $1\le \mathrm{nexp}_l\le k_0$ for $l\ge 1$, and every $B_l$, there is a real constant $C$, independent of all data below, such that: for every valuation subring $A\subseteq\bar{\mathbb Q}$ in which $p$ is a nonunit, every two extensions $\bar F,\bar F'$ of the residue field of $A$, component charts $C_1,C_1'$ of `modularFunctionFieldBar N` over $A$ with these residue fields, places $x,x'$ of $\bar F,\bar F'$, and annuli $An,An'$ with $An$ attached to $C_1$ at $x$ and $An'$ to $C_1'$ at $x'$, having equal domains, equal nonzero modulus $\pi$, and $An'.\mathrm{param}\cdot An.\mathrm{param}=\pi$; and for every $\pi_x\ne 0$ in the maximal ideal of $A$ with $\pi=u^{-1}\pi_x$ for a unit $u$ of $A$, $p^{k_0}=\pi_x a$ and $\pi_x=pb$ with $a,b\in A$, and $\pi=p\cdot(\text{unit of }A)$; provided $p^{B_l}M_{ij},p^{B_l}M^{-1}_{ij}\in A$ for all $i,j$; each $t_l$ is $C_1'$-integral with nonzero residue, of $x'$-order $\ge 1$ for $l\ge 1$, with some $l\ge 1$ of $x'$-order exactly $1$; each $p^{-\mathrm{nexp}_l}t_l$ is $C_1$-integral with nonzero residue; and for every place $R$ in $An.\mathrm{dom}$ and $l\ge 1$, $t_l$ lies in $R$'s valuation ring with $R(t_l)$ in the maximal ideal of $A$ — then for every non-archimedean absolute value $\mu$ on $\bar{\mathbb Q}$ whose unit ball is exactly $A$, and all distinct $P,Q\in An.\mathrm{dom}$ whose evaluation vectors $\mathrm{evalVec}\,s$ are non-proportional (some $2\times2$ minor nonvanishing), $$\bigl|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,P,\mathrm{evalVec}\,s\,Q)+\log\mu\bigl(P(An.\mathrm{param})-Q(An.\mathrm{param})\bigr)\bigr|\le C\cdot\bigl(-\log\mu(\pi)\bigr),$$ where $\mathrm{prox}$ is the chordal proximity $\log\sup_i\mu(x_i)+\log\sup_i\mu(y_i)-\log\sup_{i,j}\mu(x_iy_j-x_jy_i)$.
--
--   This is the analytic comparison on a node tube of the semistable model at a prime exactly dividing the level: up to a bounded multiple of the logarithmic thickness of the annulus, the chordal proximity of two points in the embedding coordinates $s$ agrees with the $\mu$-distance of their annulus parameters. It supplies the metric input to [`ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le), the uniform dual-graph covering statement at a multiplicative prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_annulusComparison_of_attached_at_both_ends_of_adaptedFamily.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.annulusComparison_of_attached_at_both_ends_of_adaptedFamily (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∀ (k₀ : ℕ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ),
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) →
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) →
    Minv * M = 1 → M * Minv = 1 →
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) → (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) →
    (∀ l, nexp l ≤ k₀) →
    ∃ (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar)
      (C' : ComponentChart A (modularFunctionFieldBar N) Fbar')
      (x : Place (ResidueField ↥A) Fbar) (x' : Place (ResidueField ↥A) Fbar')
      (An An' : Annulus A (modularFunctionFieldBar N)),
    An.IsAttached C x → An'.IsAttached C' x' →
    (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An.modulus : AlgebraicClosure ℚ))) →
    ∀ (πx : AlgebraicClosure ℚ), πx ≠ 0 → (∃ hmem : πx ∈ A, (⟨πx, hmem⟩ : A) ∈ maximalIdeal A) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) * u = πx) →
    (∃ a : AlgebraicClosure ℚ, a ∈ A ∧ (p : AlgebraicClosure ℚ) ^ k₀ = πx * a) →
    (∃ b : AlgebraicClosure ℚ, b ∈ A ∧ πx = (p : AlgebraicClosure ℚ) * b) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) * u) →
    (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) →
    (∀ l : Fin r, ∃ h : t l ∈ C'.integers,
      C'.residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ x'.ord (C'.residue ⟨t l, h⟩))) →
    (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ C'.integers, x'.ord (C'.residue ⟨t l, h⟩) = 1) →
    (∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l ∈ C.integers, C.residue ⟨_, h⟩ ≠ 0) →
    (∀ R ∈ An.dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      t l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) →
    (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q →
        (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
          ≤ Cc * (-Real.log (μ ((An.modulus : AlgebraicClosure ℚ))))) := by sorry
