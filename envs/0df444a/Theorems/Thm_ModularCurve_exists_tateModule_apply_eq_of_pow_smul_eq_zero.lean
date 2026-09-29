-- Prove2me | Theorems.Thm_ModularCurve_exists_tateModule_apply_eq_of_pow_smul_eq_zero
-- name    : ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/3a8605e4-8122-5074-a895-ef18aad4d721
-- title:
--   Surjectivity of the level maps of T_ℓ J₀(p)
-- statement:
--   Let $p$ and $\ell$ be primes, let $k$ be a natural number, and write $\mathrm{JZero}\,p$ for the group $\mathrm{Pic}^0$ attached to the base change to $\overline{\mathbf Q}$ of the full modular function field of level $p$, i.e. the quotient of the group of degree-zero divisors by the subgroup of principal divisors. Let $y \in \mathrm{JZero}\,p$ satisfy $\ell^k \cdot y = 0$. The assertion is that there exists an element $s$ of [`TateModule ℓ (JZero p)`](def/EllipticCurve_TateModule.html#L15), the additive subgroup of the group of sequences $x \colon \mathbf N \to \mathrm{JZero}\,p$ cut out by the two conditions $\ell^n \cdot x_n = 0$ and $\ell \cdot x_{n+1} = x_n$ for every $n$, whose $k$-th term, as a sequence, equals $y$. Thus the $k$-th level map from the $\ell$-adic Tate module of $\mathrm{JZero}\,p$ to its $\ell^k$-torsion hits $y$; the conclusion is an existence statement only, with no continuity, Galois- or Hecke-equivariance claim. Note that the prime $\ell$ used to form the Tate module and the level $p$ of the modular curve are unrelated.
--
--   This is the surjectivity of the level maps $T_\ell J_0(p) \to J_0(p)[\ell^k]$, a consequence of divisibility of the group of degree-zero divisor classes of a curve over an algebraically closed field. It feeds into [`ModularCurve.exists_bilinForm_tateModule_nondegenerate_hecke_galois`](thm.html#ModularCurve.exists_bilinForm_tateModule_nondegenerate_hecke_galois), where non-degenerate pairings at finite level are assembled into a pairing on the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tateModule_apply_eq_of_pow_smul_eq_zero.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (y : JZero p) (hy : ℓ ^ k • y = 0) :
    ∃ s : TateModule ℓ (JZero p), (s : ℕ → JZero p) k = y := by sorry
