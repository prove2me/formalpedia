-- Prove2me | Theorems.Thm_HuangN13_N13GaussianDifferentSupport_coe_algebraNorm_int
-- name    : HuangN13.N13GaussianDifferentSupport.coe_algebraNorm_int
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:50:47.459446+00:00
-- url     : https://prove2.me/theorems/70f2f04a-c182-4613-98b8-81ed67f8413c
-- title:
--   Integral and field norm compatibility
-- statement:
--   For the fixed integral order $O\subset L$ in the order-thirteen development, the integer algebra norm of every $x\in O$, embedded into $\mathbb Q$, equals the rational field norm of its image in $L$:
--
--   $$\iota_{\mathbb Z,\mathbb Q}(\operatorname{norm}_{O/\mathbb Z}(x))=\operatorname{Norm}_{L/\mathbb Q}(\iota_{O,L}(x)).$$
--
--   This identifies the norm in the integral-closure presentation with the field norm used in the parity argument.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT proof at https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13GaussianDifferentSupport.lean#L1328-L1349; flattened unit 6, lines1332–1353.

import Definitions.Def_MazurN13_L4

set_option autoImplicit false
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.numberFieldL MazurProof.N13GaussianDifferentSupport.intAlgebraO

theorem HuangN13.N13GaussianDifferentSupport.coe_algebraNorm_int (x : MazurProof.N13GaussianDifferentSupport.O) :
    (Algebra.norm ℤ x : ℚ) =
      Algebra.norm ℚ ((x : MazurProof.N13GaussianDifferentSupport.O) : MazurProof.N13GaussianDifferentSupport.L) := by sorry
