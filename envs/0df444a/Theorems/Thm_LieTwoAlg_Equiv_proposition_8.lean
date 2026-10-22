-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_proposition_8
-- name    : LieTwoAlg.Equiv.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:39.285162+00:00
-- url     : https://prove2.me/theorems/bd5bed66-05b4-483d-b4f4-d63f5d283554
-- title:
--   Proposition 8, p. 12 — the categories 2Vect and 2Term are equivalent
-- statement:
--   Let $k$ be any field. A **2-vector space** $V$ consists of vector spaces $V_0$ (objects) and $V_1$ (morphisms) with linear source, target and identity maps $s,t\colon V_1\to V_0$, $i\colon V_0\to V_1$ satisfying $s\circ i=t\circ i=\mathrm{id}$; its composition is the one forced by Lemma 6. A morphism of 2-vector spaces is a **linear functor** $F=(F_0,F_1)$, a pair of linear maps commuting with $s$, $t$ and $i$. A **2-term chain complex** $C$ is a linear map $d\colon C_1\to C_0$, and a morphism is a **chain map** $(\varphi_0,\varphi_1)$ with $d'\varphi_1=\varphi_0 d$.
--
--   The category $\mathbf{2Vect}$ of 2-vector spaces and linear functors is equivalent to the category $\mathbf{2Term}$ of 2-term chain complexes and chain maps:
--
--   $$
--   \mathbf{2Vect}\;\simeq\;\mathbf{2Term}.
--   $$
--
--   That is, both are categories, and there are functors $S\colon\mathbf{2Vect}\to\mathbf{2Term}$ and $T\colon\mathbf{2Term}\to\mathbf{2Vect}$ together with natural isomorphisms $TS\Rightarrow 1$ and $ST\Rightarrow 1$.
--
--   This is the linear-algebra layer underneath Theorem 36: a Lie 2-algebra and a 2-term $L_\infty$-algebra have, respectively, a 2-vector space and a 2-term chain complex as underlying object, and the functors of Theorem 36 restrict to these.
--
--   **Formalization Note** Categories are encoded as raw data (objects, morphism data, a predicate selecting the lawful morphisms, identity and diagrammatic composite); `RawCat.Equivalent` asserts the category laws for both sides, functors $S,T$ preserving lawful morphisms, identities and composites, and invertible natural components. The triangle identities of an adjoint equivalence are not required, as in the textbook definition of an equivalence of categories.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, p. 12, Proposition 8

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Proposition 8, p. 12: the categories 2Vect and 2Term are equivalent. -/
theorem proposition_8 (k : Type u) [Field k] :
    RawCat.Equivalent (twoVectCat k) (twoTermCat k) := by sorry

end LieTwoAlg.Equiv
