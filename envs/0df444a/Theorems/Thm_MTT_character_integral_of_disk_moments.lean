-- Prove2me | Theorems.Thm_MTT_character_integral_of_disk_moments
-- name    : MTT.character_integral_of_disk_moments
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:49:14.533446+00:00
-- url     : https://prove2.me/theorems/434ef507-a279-40f1-8766-9cc2f2ad451a
-- title:
--   Character integrals are finite sums of prescribed disk moments
-- statement:
--   Let a bounded measure on the p-adic units realize the prescribed signed polynomial disk moments for an eigenform and its period system. At any positive depth $n$ and critical degree $j$, every Dirichlet character modulo $p^n$ gives a continuous function $x\mapsto\chi(x)x^j$, whose integral is the sum of the disk moments multiplied by the corresponding character values over the invertible residue classes modulo $p^n$. Character values are transported through the specified embedding into $\mathbf C_p$. Primitivity of the character and ordinarity of the root are not required for this finite reconstruction.
-- source:
--   Mazur–Tate–Teitelbaum, Invent. Math. 84 (1986), Chapter I, (10.2) and §14, https://doi.org/10.1007/BF01388731. Elementary finite-residue-disk reconstruction supporting the interpolation formula.

import Definitions.Def_MTT_Measures
open MTT
open scoped BigOperators

theorem MTT.character_integral_of_disk_moments {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool) (μ : UnitMeasure p)
    (hμ : RealizesMoments f ιp P α s μ)
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (j : ℕ) (hj : j ≤ k - 2) :
    ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      μ g = ∑ a : (ZMod (p ^ n))ˣ,
        ιp (χ a) * diskMoment f ιp P α s j n ((a : ZMod (p ^ n)).val : ℤ) := by sorry
