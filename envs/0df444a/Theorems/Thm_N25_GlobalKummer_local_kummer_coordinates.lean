-- Prove2me | Theorems.Thm_N25_GlobalKummer_local_kummer_coordinates
-- name    : N25.GlobalKummer.local_kummer_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:15.01112+00:00
-- url     : https://prove2.me/theorems/9e29202f-2a79-4920-8d6f-c006ee10521f
-- title:
--   Global Kummer data admit equivariant $71$-adic coordinates
-- statement:
--   Let $c\in Z^1(G_{ℚ},𝔽_{71}(χ_{71}))$, let $e:𝔽_{71}\to μ_{71}(ℚ̄)$ be an equivariant additive isomorphism, and let $a\in ℚ^×$, $α\in ℚ̄^×$ satisfy $α^{71}=a$ and $e(c(σ))=σ(α)/α$. Write $ι_{71}:ℚ̄\to\overline{ℚ}_{71}$ for the chosen embedding and $G_{71}=\mathrm{Gal}(\overline{ℚ}_{71}/ℚ_{71})$. Then there is an injective map $μ:𝔽_{71}\to\overline{ℚ}_{71}$ such that $$μ(0)=1,\quad μ(b+d)=μ(b)μ(d),\quad μ(b)^{71}=1,\quad μ(ρ_{\mathrm{cyc},71}(τ)b)=τ(μ(b)),$$ $$ι_{71}(α)^{71}=a,\qquad μ(c(τ|_{G_{ℚ}}))\,ι_{71}(α)=τ(ι_{71}(α))\quad(τ\in G_{71}).$$ This converts the global cyclotomic cocycle into explicit local Kummer coordinates at $71$. Formalization note: the two displayed algebra maps identify the rational number $a$ inside the $71$-adic algebraic closure.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_N25_LocalFiniteFlatClasses

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance localCoordinatesPrimeSeventyOne_ic39b60 : Fact (Nat.Prime 71) := ⟨by decide⟩
local instance localCoordinatesScalarTower_ic39b60 : IsScalarTower ℚ ℚ_[71] (PadicAlgCl 71) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem N25.GlobalKummer.local_kummer_coordinates
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (he : ∀ (σ : Gal) (a : ZMod 71),
      e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
        Additive.ofMul (σ • Additive.toMul (e a)))
    (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ) :
    ∃ μ : ZMod 71 → PadicAlgCl 71,
      Function.Injective μ ∧ μ 0 = 1 ∧
      (∀ b d, μ (b + d) = μ b * μ d) ∧
      (∀ b, μ b ^ 71 = 1) ∧
      (∀ (σ : PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71) (b : ZMod 71),
        μ (localCyclotomicRep.ρ σ b) = σ (μ b)) ∧
      (padicEmbedding 71 (α : AlgebraicClosure ℚ)) ^ 71 =
        algebraMap ℚ_[71] (PadicAlgCl 71) (algebraMap ℚ ℚ_[71] (a : ℚ)) ∧
      ∀ σ : PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71,
        μ (c (localGaloisToGlobal 71 σ)) * padicEmbedding 71 (α : AlgebraicClosure ℚ) =
          σ (padicEmbedding 71 (α : AlgebraicClosure ℚ)) := by sorry
