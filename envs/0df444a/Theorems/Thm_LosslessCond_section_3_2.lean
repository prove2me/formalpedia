-- Prove2me | Theorems.Thm_LosslessCond_section_3_2
-- name    : LosslessCond.section_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:12.129194+00:00
-- url     : https://prove2.me/theorems/1805360e-3b75-4e29-80b8-fea59c88cccc
-- title:
--   §3.2, (3.1) — leaf conditions and the intersection/union recursion for $G_P(U)$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a Boolean matrix and $U\subseteq X$ any row set (possibly empty).
--
--   1. At a leaf labelled $b$, the accepted columns are exactly
--   $$
--   G_{\mathrm{leaf}\,b}(U)=\{y\in Y:\ M(x,y)=b\ \text{for every } x\in U\}. \tag{3.1}
--   $$
--   2. At an Alice node sending $f$ with children $P_0,P_1$, both row groups must be served:
--   $$
--   G_P(U)=G_{P_0}(U\cap\{f=0\})\cap G_{P_1}(U\cap\{f=1\}).
--   $$
--   3. At a Bob node with children $P_0,P_1$, Bob may select one child for all the rows:
--   $$
--   G_P(U)=G_{P_0}(U)\cup G_{P_1}(U).
--   $$
--
--   Hence every protocol domain is a depth-$s$ intersection/union tree of leaf conditions, which is what Lemma 4.3 counts.
--
--   Differences from the source:
--   - encoding: the rows associated with a node (consistent with Alice's choices along the path) → U ∩ {x | f x = false} and U ∩ {x | f x = true} at an Alice node, U unchanged at a Bob node; reason: this is the paper's description of the associated rows, one level at a time
--   - generalization: finite input sets → arbitrary types X, Y; reason: the equations hold without finiteness; finite X, Y are a special case
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), §3.2, (3.1) and the following paragraph, p.9 (PDF p.10); "Formally, this description follows by induction", p.9

import Mathlib
import Definitions.Def_LosslessCond_domain

namespace LosslessCond

/-- **The conditions at a leaf and the intersection/union recursion** (Mackenzie, *Lossless
Hardness Condensation in Deterministic Communication Complexity*, arXiv:2609.28691, held version
sha256 ce75e6d4…, §3.2, pp.8–9, (3.1)). For every row set `U`:

1. at a leaf labelled `b`, the accepted columns are exactly
   `{y ∈ Y : M(x, y) = b for every associated row x}` (3.1);
2. at an Alice node sending `f`, the accepted columns are the intersection of the child sets, the
   child `p₀` serving the rows of `U` with `f x = 0` and `p₁` those with `f x = 1`;
3. at a Bob node, the accepted columns are the union of the child sets, each child serving all of
   `U`.

**Formalization Note** `domain` is defined by one assignment of bits to all Bob nodes
(Definition 3.1), so these equations are the content of "Formally, this description follows by
induction on the subtree height" (p.9) and not definitional. -/
theorem section_3_2 {X Y : Type} (M : X → Y → Bool) :
    (∀ (b : Bool) (U : Set X),
      domain M (PartialProtocol.leaf b) U = {y | ∀ x ∈ U, M x y = b}) ∧
    (∀ (s : ℕ) (f : X → Bool) (p₀ p₁ : PartialProtocol X s) (U : Set X),
      domain M (PartialProtocol.alice f p₀ p₁) U =
        domain M p₀ (U ∩ {x | f x = false}) ∩ domain M p₁ (U ∩ {x | f x = true})) ∧
    (∀ (s : ℕ) (p₀ p₁ : PartialProtocol X s) (U : Set X),
      domain M (PartialProtocol.bob p₀ p₁) U = domain M p₀ U ∪ domain M p₁ U) := by sorry

end LosslessCond
