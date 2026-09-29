-- Prove2me | Theorems.Thm_MTT_Cohomology_act_one
-- name    : MTT.Cohomology.act_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:43:10.397134+00:00
-- url     : https://prove2.me/theorems/16fc0341-eb8c-45b2-9395-db816d3be5eb
-- title:
--   The coefficient action of the identity matrix is the identity
-- statement:
--   The coefficient action of a matrix $\gamma\in M_2(\mathbf Z)$ on binary polynomials over a commutative ring $R$ is the substitution $X_i\mapsto\sum_a\gamma_{ai}X_a$. For $\gamma=I$ this substitution is $X_i\mapsto X_i$, so it acts as the identity on $R[X_0,X_1]$:
--   $$1\cdot P = P\quad\text{for all }P.$$
--   Together with multiplicativity this says that $\gamma\mapsto(\text{act }\gamma)$ is a monoid homomorphism from $M_2(\mathbf Z)$ to the $R$-algebra endomorphisms of $R[X_0,X_1]$, hence a genuine action of $\mathrm{SL}_2(\mathbf Z)$ (and of the Hecke monoid) on the graded pieces $\mathrm{Sym}^n$.
-- source:
--   Standard functoriality of the right coefficient action on Sym^n; cf. Ash-Stevens, Modular forms in characteristic l and special values of their L-functions, Duke Math. J. 53 (1986), section 1, pp. 850-852, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.act_one {R : Type*} [CommRing R] (P : Binary R) :
    act (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by sorry
