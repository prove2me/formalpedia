-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_realCriterion_cospherical
-- name    : OAI.EuclideanRamsey.realCriterion_cospherical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:21:49.569411+00:00
-- url     : https://prove2.me/theorems/68d407a0-e25d-4fca-be11-fc79292b032f
-- title:
--   The real tensor criterion forces a configuration onto a sphere
-- statement:
--   Let $T=\mathbb R\otimes_{\mathbb Q}\mathbb R$, with multiplication map $m:T\to\mathbb R$, $x\otimes y\mapsto xy$. A real array of size $d$ is a matrix $P=(P_{\alpha\beta})$ indexed by $\alpha,\beta\in\{0,1,\dots,d\}$ with entries in $T$, where the index $0$ stands for the constant term. For a configuration $a_0,\dots,a_{s-1}\in\mathbb R^d$, let $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$, and
--   $$
--   E_i(P)=\sum_{\alpha,\beta}\bigl(\tilde a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\tilde a_i(\beta)\bigr)\in T .
--   $$
--   The real criterion asks for an array $P$ with $E_i(P)=0$ for every $i$ and with spatial block $\bigl(m(P_{jk})\bigr)_{j,k\ge1}$ equal to the identity matrix. If $s>0$ and the real criterion holds for $a$, then there are a centre $c\in\mathbb R^d$ and a radius $\rho$ with
--   $$
--   |a_i-c|=\rho\qquad\text{for every }i .
--   $$
--
--   This is the last step from the algebraic criterion satisfied by Ramsey configurations to their sphericity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorSphere.lean#L17-L89

import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical

open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace

theorem OAI.EuclideanRamsey.realCriterion_cospherical {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (h : RealCriterion a) :
    EuclideanGeometry.Cospherical (Set.range a) := by sorry
