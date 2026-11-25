-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_kernel_coloring
-- name    : GalvinMultigraph.Local.kernel_coloring
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:29.243089+00:00
-- url     : https://prove2.me/theorems/a87051fb-75a1-4a09-b35c-baaf56c8c24f
-- title:
--   Local: kernel coloring
-- statement:
--   **Kernel colouring lemma.** If every induced subdigraph of `A` has a kernel and
--   `|L(v)| ≥ d⁺(v) + 1`, the underlying graph is `L`-colourable.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Kernel.lean#L32-L48
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Kernel.lean#L32-L48

module
public import Definitions.Def_GalvinLib_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Kernel
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Local
variable {V : Type*} [Fintype V]

theorem GalvinMultigraph.Local.kernel_coloring (A : V → V → Prop) [DecidableRel A]
    (hirr : ∀ v, ¬ A v v)
    (hker : ∀ S : Finset V, ∃ K, IsKernelOn A S K)
    (L : V → Finset ℕ)
    (hL : ∀ v, (Finset.univ.filter fun u => A v u).card + 1 ≤ (L v).card) :
    ∃ φ : V → ℕ, (∀ v, φ v ∈ L v) ∧ ∀ u v, A u v → φ u ≠ φ v := by sorry
