-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left
-- name    : MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a0aa475c-85f9-50af-85fe-1520f24feef0
-- title:
--   Translation-invariant measures on G× Y are μ⊗σ
-- statement:
--   Let $G$ be an additive group carrying a topology making it a topological additive group, assumed locally compact and second countable, and equipped with its Borel $\sigma$-algebra; let $\mu$ be a measure on $G$ which is an additive Haar measure. Let $Y$ be a measurable space and let $\rho$ be a measure on the product measurable space $G \times Y$. Assume two hypotheses. First, invariance under translation in the first coordinate: for every $a \in G$, the pushforward of $\rho$ along $(g,y) \mapsto (a+g, y)$ equals $\rho$. Second, a local finiteness condition along a measurable exhaustion of $Y$: there is a sequence $B : \mathbb{N} \to \mathrm{Set}\ Y$ of measurable sets with $\bigcup_n B_n = Y$ such that for every $n$ and every compact $K \subseteq G$ one has $\rho(K \times B_n) < \infty$. The conclusion asserts the existence of a measure $\sigma$ on $Y$ which is $\sigma$-finite and satisfies $\rho = \mu \otimes \sigma$, the product of $\mu$ and $\sigma$. No uniqueness of $\sigma$ is claimed, and no explicit formula for $\sigma$ is part of the statement.
--
--   This is the uniqueness of Haar measure "with parameters": each slice $E \mapsto \rho(E \times B)$ is a translation-invariant Borel measure on $G$ that is finite on compacta, hence a multiple of $\mu$, and the multiplier is a measure in $B$. It serves as the measure-theoretic device for unfolding integrals along a closed abelian (e.g. unipotent) subgroup once the ambient space has been identified equivariantly with a product $G \times Y$, and is used in the estimates for Weyl-element unipotent integrals of automorphic forms and in the global zeta-integral arguments of Tate's thesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

theorem MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    {Y : Type*} [MeasurableSpace Y] (ρ : MeasureTheory.Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ρ (K ×ˢ B n) < ⊤) :
    ∃ σ : MeasureTheory.Measure Y, MeasureTheory.SigmaFinite σ ∧ ρ = μ.prod σ := by sorry
