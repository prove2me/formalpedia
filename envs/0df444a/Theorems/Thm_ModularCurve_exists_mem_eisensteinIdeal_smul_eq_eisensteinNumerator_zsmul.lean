-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_eisensteinIdeal_smul_eq_eisensteinNumerator_zsmul
-- name    : ModularCurve.exists_mem_eisensteinIdeal_smul_eq_eisensteinNumerator_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/286a15ba-418f-582e-96b9-0af5e5ea3b6b
-- title:
--   Eisenstein ideal element acting as n(p) on J₀(p)
-- statement:
--   Let $p$ be a prime. Work with the abstract Hecke algebra `HeckeAlg` $= \mathbb{Z}[T_\ell : \ell \text{ prime}]$, realised as the polynomial ring `MvPolynomial Nat.Primes ℤ`, and with its Eisenstein ideal `eisensteinIdeal p`, defined as the kernel of the $\mathbb{Z}$-algebra map sending the variable at a prime $\ell$ to $1$ if $\ell \mid p$ and to $1+\ell$ otherwise. Let `JZero p` be the group $\mathrm{Pic}^0$ of the modular curve of level $p$ over $\overline{\mathbb{Q}}$, that is, the quotient of the degree-zero divisors by the principal divisors for the function field `modularFunctionFieldBar p` obtained from the full modular function field of level $p$ by base change to $\overline{\mathbb{Q}}$; it carries the `HeckeAlg`-module structure `heckeModuleBar p`, which is the one induced by the ring map `heckeEvalBar` sending each variable to the corresponding Hecke correspondence when these correspondences commute, and otherwise the degenerate structure in which a polynomial acts through its value at $0$. Put `eisensteinNumerator p` $= (p-1)/\gcd(p-1,12)$, the numerator of $(p-1)/12$. The assertion is that some element $i$ of `eisensteinIdeal p` satisfies $i \cdot x = (\mathrm{num}((p-1)/12)) \, x$ for every $x \in$ `JZero p`, the right-hand side being the integer scalar action on the abelian group.
--
--   This is the inclusion half of Mazur's description of the Eisenstein quotient, $\mathbb{T}_J/\mathfrak{i}_J \cong \mathbb{Z}/n$ with $n$ the numerator of $(p-1)/12$: it says that $n$ lies in the image of the Eisenstein ideal in the ring of endomorphisms of $J_0(p)$ through which the abstract Hecke algebra acts. It is used in the statements bounding the Eisenstein ideal image in cokernels, in the vanishing of the Eisenstein torsion of $J_0(p)$, and in the inertia-action statements built on that torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_eisensteinIdeal_smul_eq_eisensteinNumerator_zsmul.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_mem_eisensteinIdeal_smul_eq_eisensteinNumerator_zsmul (p : ℕ) [Fact p.Prime] : ∃ i ∈ eisensteinIdeal p, ∀ x : JZero p, (letI := heckeModuleBar p; i • x) = (eisensteinNumerator p : ℤ) • x := by sorry
