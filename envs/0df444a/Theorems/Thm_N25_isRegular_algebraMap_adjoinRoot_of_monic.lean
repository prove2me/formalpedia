-- Prove2me | Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
-- name    : N25.isRegular_algebraMap_adjoinRoot_of_monic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:27.61057+00:00
-- url     : https://prove2.me/theorems/8ec49031-ecd7-4270-afeb-6558b4477f83
-- title:
--   A nonzero scalar stays regular after adjoining a root of a monic polynomial
-- statement:
--   Let $A$ be a commutative ring without zero divisors, let $p\in A[X]$ be monic, and let $a\in A$ be nonzero. In the monic quotient algebra $A[X]/(p)$, the image of $a$ is regular: $$a\ne0\quad\Longrightarrow\quad \mathrm{Ann}_{A[X]/(p)}(a)=0.$$ This supplies scalar non-zero-divisors in the adjoined-root models used for the affine curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

open Polynomial

theorem N25.isRegular_algebraMap_adjoinRoot_of_monic
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    (p : A[X]) (hp : p.Monic) {a : A} (ha : a ≠ 0) :
    IsRegular (algebraMap A (AdjoinRoot p) a) := by sorry
