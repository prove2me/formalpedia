-- Prove2me | Theorems.Thm_GrandUnifiedTheories_phi_map_mul
-- name    : GrandUnifiedTheories.phi_map_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:41:59.942485+00:00
-- url     : https://prove2.me/theorems/178524c8-141e-4be9-8f28-7c3a804a61e6
-- title:
--   $\varphi$ is a group homomorphism
-- statement:
--   The Georgi-Glashow map $\varphi$ is multiplicative: for all $x, y \in G_{\mathrm{SM}}$,
--
--   $$\varphi(xy) \;=\; \varphi(x)\,\varphi(y),$$
--
--   where the product on the left is the componentwise product of $\mathrm{U}(1)\times\mathrm{SU}(2)\times\mathrm{SU}(3)$ and the product on the right is matrix multiplication of $5\times5$ complex matrices.
--
--   Together with the previous milestone this makes $\varphi$ a homomorphism of Lie groups $G_{\mathrm{SM}}\to\mathrm{SU}(5)$, which is the statement "$\varphi$ is clearly a homomorphism" of the source, and the precondition for speaking of its kernel and image.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.1, p. 34 ('It is clearly a homomorphism', immediately after the displayed definition of φ)

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem phi_map_mul (x y : GSM) :
    phiMatrix (x * y) = phiMatrix x * phiMatrix y := by sorry

end GrandUnifiedTheories
