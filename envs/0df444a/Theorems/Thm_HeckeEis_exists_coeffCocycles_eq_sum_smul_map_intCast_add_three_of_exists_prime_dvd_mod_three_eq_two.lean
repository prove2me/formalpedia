-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
-- name    : HeckeEis.exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/b16400df-90cd-5823-a035-5ea9d1e8c681
-- title:
--   Mod-3 cocycles for Γ₀(N) come from integral ones
-- statement:
--   Let $F$ be a field of characteristic $3$, let $n, N$ be natural numbers with $N \neq 0$, and assume there is a prime $q$ with $q \mid N$ and $q \equiv 2 \pmod 3$. Write $\mathrm{BinaryForm}\,K\,n$ for the submodule of degree-$n$ homogeneous elements of $K[X_0,X_1]$, and let $\mathrm{SL}_2(\mathbb{Z})$ act on it by the substitution $X_j \mapsto \sum_i M_{ij} X_i$ attached to $M$; restrict this representation along the inclusion of $\Gamma_0(N)$. Let $z$ be a cocycle for the $F$-valued restricted representation, i.e. a function $z : \Gamma_0(N) \to \mathrm{BinaryForm}\,F\,n$ with $z(gh) = z(g) + \rho(g)(z(h))$ for all $g,h$. The assertion is that there exist a natural number $m$, scalars $c : \mathrm{Fin}\,m \to F$, cocycles $y_i : \Gamma_0(N) \to \mathrm{BinaryForm}\,\mathbb{Z}\,n$ for the corresponding $\mathbb{Z}$-valued representation, and a function $w : \Gamma_0(N) \to \mathrm{BinaryForm}\,F\,n$ lying in the coboundaries, that is $w(g) = \rho(g)v - v$ for a single $v \in \mathrm{BinaryForm}\,F\,n$, such that for every $g \in \Gamma_0(N)$ one has the identity of polynomials $z(g) = \sum_{i} c_i \cdot \big(y_i(g) \bmod 3\big) + w(g)$, the reduction being coefficientwise application of $\mathbb{Z} \to F$.
--
--   This is the surjectivity, at the characteristic-$3$ place and for levels divisible by a prime $q \equiv 2 \pmod 3$, of the natural map $H^1(\Gamma_0(N), \mathrm{Sym}^n \mathbb{Z}^2) \otimes F \to H^1(\Gamma_0(N), \mathrm{Sym}^n F^2)$, stated at the level of explicit inhomogeneous cocycles rather than cohomology classes: the hypothesis on $q$ removes order-$3$ elements from the image of $\Gamma_0(N)$ in $\mathrm{PSL}_2(\mathbb{Z})$, replacing the usual restriction to residue characteristics at least $5$. It is used in the construction of mod-$3$ eigenforms from eigensystems occurring in the cohomology of the binary-form representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffCocycles_eq_sum_smul_map_intCast_add_three_of_exists_prime_dvd_mod_three_eq_two
    (F : Type) [Field F] [CharP F 3] (n N : ℕ) [NeZero N] (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ (m : ℕ) (c : Fin m → F)
      (y : Fin m → ↥(HeckeEis.coeffCocycles
        ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
      (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)),
      w ∈ HeckeEis.coeffCoboundaries
          ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype) ∧
        ∀ g : CongruenceSubgroup.Gamma0 N,
          (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F)) =
            (∑ i : Fin m, c i • MvPolynomial.map (Int.castRingHom F)
                (((y i : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g :
                  MvPolynomial (Fin 2) ℤ))) +
              ((w g : ↥(HeckeEis.BinaryForm F n)) : MvPolynomial (Fin 2) F) := by sorry
