-- Prove2me | Theorems.Thm_GrandUnifiedTheories_phi_range_eq
-- name    : GrandUnifiedTheories.phi_range_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:51:11.114541+00:00
-- url     : https://prove2.me/theorems/a0b86fa1-c9f1-400b-97f0-721266a771f0
-- title:
--   The image of $\varphi$ is $S(\mathrm{U}(2)\times\mathrm{U}(3))$
-- statement:
--   A complex $5\times5$ matrix $A$ is of the form $\varphi(x)$ for some $x\in G_{\mathrm{SM}}$ if and only if $A$ lies in $\mathrm{SU}(5)$ and is block diagonal for the splitting $\mathbb{C}^5\cong\mathbb{C}^2\oplus\mathbb{C}^3$, i.e. $A$ maps $\mathbb{C}^2$ to $\mathbb{C}^2$ and $\mathbb{C}^3$ to $\mathbb{C}^3$. In other words,
--
--   $$\operatorname{im}\varphi \;=\; S\bigl(\mathrm{U}(2)\times\mathrm{U}(3)\bigr) \;=\; \Bigl\{\begin{pmatrix}P&0\\0&Q\end{pmatrix} : P\in\mathrm{U}(2),\ Q\in\mathrm{U}(3),\ \det P\,\det Q = 1\Bigr\}.$$
--
--   Combined with the kernel computation, this is the isomorphism
--
--   $$G_{\mathrm{SM}}/\mathbb{Z}_6 \;\cong\; S(\mathrm{U}(2)\times\mathrm{U}(3)) \hookrightarrow \mathrm{SU}(5)$$
--
--   of the source: the true Standard Model gauge group is exactly the subgroup of $\mathrm{SU}(5)$ preserving the $2+3$ splitting of $\mathbb{C}^5$. The nontrivial half is surjectivity, which requires extracting a sixth root inside $\mathrm{U}(1)$ of the determinant of the $\mathrm{U}(2)$ block.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.1, p. 34 ('It clearly maps G_SM into the subgroup S(U(2) × U(3)), and it is easy to check that it maps G_SM onto this subgroup', and the resulting isomorphism G_SM/Z₆ ≅ S(U(2) × U(3)) ↪ SU(5))

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem phi_range_eq (A : Matrix Idx5 Idx5 ℂ) :
    (∃ x : GSM, phiMatrix x = A) ↔
      (A ∈ Matrix.specialUnitaryGroup Idx5 ℂ ∧
        ∀ i j, A (Sum.inl i) (Sum.inr j) = 0 ∧ A (Sum.inr j) (Sum.inl i) = 0) := by sorry

end GrandUnifiedTheories
