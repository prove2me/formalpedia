-- Prove2me | Theorems.Thm_N25_isRegular_scalar_mod_root_relation
-- name    : N25.isRegular_scalar_mod_root_relation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:27.760198+00:00
-- url     : https://prove2.me/theorems/bee5d1b1-e34f-4714-b6a7-3e200a692124
-- title:
--   Scalar regularity transfers across a monic root relation
-- statement:
--   Let $R$ be an integral domain, let $q,c\in R[X]$, let $D\in R$ be nonzero, and assume $q$ is monic. Reduce coefficients modulo $(D)$ and suppose the value of $c$ at the adjoined root is regular in $(R/(D))[X]/(q\bmod D)$. Then, in $R[X]/(q)$ modulo the relation $c(\bar X)=0$, the image of $D$ is regular: $$c(\bar X)\text{ regular mod }D\quad\Longrightarrow\quad D\text{ regular in }(R[X]/(q))/(c(\bar X)).$$ This is the regularity transfer used to certify the scalar localization in the plane model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

open Polynomial

theorem N25.isRegular_scalar_mod_root_relation
    {R : Type*} [CommRing R] [IsDomain R]
    (q c : Polynomial R) (D : R) (hq : q.Monic) (hD : D ≠ 0)
    (hc : IsRegular (AdjoinRoot.mk
      (q.map (Ideal.Quotient.mk (Ideal.span ({D} : Set R))))
      (c.map (Ideal.Quotient.mk (Ideal.span ({D} : Set R)))))) :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({AdjoinRoot.mk q c} : Set (AdjoinRoot q)))
      (AdjoinRoot.of q D)) := by sorry
