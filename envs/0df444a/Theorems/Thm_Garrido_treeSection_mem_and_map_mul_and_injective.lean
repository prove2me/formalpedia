-- Prove2me | Theorems.Thm_Garrido_treeSection_mem_and_map_mul_and_injective
-- name    : Garrido.treeSection_mem_and_map_mul_and_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:09:48.443992+00:00
-- url     : https://prove2.me/theorems/d92dec5c-10cc-410c-a012-73e4816c19fe
-- title:
--   p. 14 — ψ : St(1) → Γ × Γ and ψₙ : St(n) → Γ^(2ⁿ) are monomorphisms
-- statement:
--   The map $\psi : St(1) \to \Gamma \times \Gamma$, $g \mapsto (g_0, g_1)$, is a monomorphism; and
--   similarly, for every $n$, so is $\psi_n : St(n) \to \Gamma^{2^n}$, sending $g$ to its sections at
--   the $2^n$ vertices of level $n$. In each case the sections lie in $\Gamma$, the map is
--   multiplicative, and it is injective.
--
--   $$\psi : St(1) \hookrightarrow \Gamma \times \Gamma, \qquad \psi_n : St(n) \hookrightarrow \Gamma^{2^n}, \quad g \mapsto (g|_v)_{|v| = n}.$$
--
--   It is what lets the growth of $\Gamma$ be estimated through the growth of its sections.
--
--   **Formalization Note.** $\psi$ is the imported `stOnePair`, the notes' pair $(g_0, g_1)$, whose
--   components are automorphisms of the tree: the first three conjuncts say both components lie in
--   $\Gamma$, the pair of a product is the componentwise product of the pairs, and `stOnePair` is
--   injective. For $\psi_n$ the vertices of level $n$ are indexed by $v : \mathrm{Fin}\,n \to$ `Bool`
--   through `List.ofFn`, and the three statements are made vertex by vertex: each section lies in
--   $\Gamma$; the section of a product is the product of the sections; two elements of $St(n)$ with the
--   same sections are equal.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, the Remark after Definition 4.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem treeSection_mem_and_map_mul_and_injective :
    ((∀ g : levelStabilizer 1,
        (stOnePair g).1 ∈ GrigorchukGroup ∧ (stOnePair g).2 ∈ GrigorchukGroup) ∧
      (∀ g h : levelStabilizer 1, stOnePair (g * h) = stOnePair g * stOnePair h) ∧
      Function.Injective stOnePair) ∧
    ∀ n : ℕ,
      (∀ g : GrigorchukGroup, g ∈ levelStabilizer n → ∀ v : Fin n → Bool,
          treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup) ∧
        (∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          ∀ v : Fin n → Bool, treeSection ((g * h : GrigorchukGroup) : BinaryTreeAut) (List.ofFn v) =
            treeSection (g : BinaryTreeAut) (List.ofFn v) * treeSection (h : BinaryTreeAut) (List.ofFn v)) ∧
        ∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          (∀ v : Fin n → Bool, treeSection (g : BinaryTreeAut) (List.ofFn v) =
            treeSection (h : BinaryTreeAut) (List.ofFn v)) → g = h := by
  sorry

end Garrido
