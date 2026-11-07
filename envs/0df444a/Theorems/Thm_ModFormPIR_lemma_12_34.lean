-- Prove2me | Theorems.Thm_ModFormPIR_lemma_12_34
-- name    : ModFormPIR.lemma_12_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:27.353461+00:00
-- url     : https://prove2.me/theorems/72b79ae4-eee5-4d89-a872-be18ccabf984
-- title:
--   Lemma 12.34 with Corollary 12.33, p.75 — $B^2$ is a modular form, with $\mathrm{ord}_c(B^2)\ge d/4+2\ell_c+2H_c$
-- statement:
--   Let $q$ be an odd prime, $q\mid d$, $\beta$ with (42)–(44), and $\rho$ the Weil representation with $\mu=(q+1)/2$. For all cusps $c$, $B^2$ is holomorphic at $c$ and
--   $$\mathrm{ord}_c(B^2)\ge\frac d4+2\ell_c+2H_c.$$
--   Thus $B^2$ is a modular form for $\Gamma(q)$ of weight $3d$, with a one-dimensional representation of finite order.
--
--   This is the second scalarization, by evaluation at the $2$-torsion points; the valence formula applied to it gives Lemma 12.42.
--
--   Differences from the source:
--   - generalization: a witness β with (42)–(45), which by Theorem 12.2 does not exist → every β with (42)–(44), q ∣ d; reason: the proof uses only these; the general form is satisfiable (β = 1 on {b𝟏}), and the printed one would be vacuous
--   - encoding: cusp c with a fixed matrix g_c → every g ∈ SL₂(ℤ), with ℓ_g, H_g from g; reason: "any fixed choice" in §12.5.1; a cusp is g∗∞
--   - encoding: ord_c from Fourier expansion (24)–(25) → sup of r with f_g(τ) e^{−2πirτ/q} bounded as Im τ → ∞; reason: equivalent for a scalar with a finite-order character; checked in the sanity file on Δ
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 12.34 and the sentence after its proof, with Corollary 12.33, p.75 (PDF p.79)

import Mathlib
import Definitions.Def_ModFormPIR_CharForms
import Definitions.Def_ModFormPIR_Witness

open scoped MatrixGroups

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 12.34** with Corollary 12.33 and the sentence after the proof, p.75. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
`B²` is a modular form for `Γ(q)` of weight `3d` with a one-dimensional representation of finite order, holomorphic at every cusp, and `ord_c(B²) ≥ d/4 + 2ℓ_c + 2H_c`.

**Formalization Note.** As in Lemma 12.29: for every `β` with (42)–(44), and every lift `g` of a cusp, with `ℓ_g, H_g` from that lift. -/
theorem lemma_12_34 (q d : ℕ) [Fact q.Prime] (hodd : Odd q) (hd : 1 ≤ d) (hqd : q ∣ d)
    (β : (Fin d → ZMod q) → ℂ) (hβ : IsNormalizedWitness β)
    (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (hρ : IsWeil q (muHalf q) ρ) :
    IsModularFormChar q (3 * d) (fun τ => Bprod β τ ^ 2) ∧
      ∀ g : SL(2, ℤ),
        (((d : ℝ) / 4 + 2 * ellG ρ β g + 2 * HG ρ β g : ℝ) : EReal) ≤
          cuspOrd q (3 * d) (fun τ => Bprod β τ ^ 2) g := by sorry

end ModFormPIR
