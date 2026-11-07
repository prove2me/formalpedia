-- Prove2me | Theorems.Thm_ModFormPIR_lemma_12_29
-- name    : ModFormPIR.lemma_12_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:56.174512+00:00
-- url     : https://prove2.me/theorems/0cda91da-dcfa-4095-b0f2-55bdb19fa04b
-- title:
--   Lemma 12.29, p.73 — $A_m^2$ is a modular form, with $\mathrm{ord}_c(A_m^2)\ge d/4+2\ell_c$
-- statement:
--   Let $q$ be an odd prime, $q\mid d$, $\beta$ with (42)–(44), and $\rho$ the Weil representation with $\mu=(q+1)/2$. Let $m$ be minimal with $A_m\not\equiv0$. Then $A_m^2:\mathbb H\to\mathbb C$ is a modular form for $\Gamma(q)$ of weight $d+2m$ with a one-dimensional representation of finite order, and for all cusps $c$,
--   $$\mathrm{ord}_c(A_m^2)\ge\frac d4+2\ell_c.$$
--
--   This is the first scalarization; the valence formula applied to it gives Lemma 12.41.
--
--   Differences from the source:
--   - generalization: a witness β with (42)–(45), which by Theorem 12.2 does not exist → every β with (42)–(44), q ∣ d; reason: the proof uses only these; the general form is satisfiable (β = 1 on {b𝟏}), and the printed one would be vacuous
--   - encoding: cusp c with a fixed matrix g_c → every g ∈ SL₂(ℤ), with ℓ_g, H_g from g; reason: "any fixed choice" in §12.5.1; a cusp is g∗∞
--   - encoding: ord_c from Fourier expansion (24)–(25) → sup of r with f_g(τ) e^{−2πirτ/q} bounded as Im τ → ∞; reason: equivalent for a scalar with a finite-order character; checked in the sanity file on Δ
--   - encoding: "there exists a minimal m" (Proposition 12.21), ℓ_c well-defined (Corollary 12.22) → clauses ∃ m and nonempty levels; reason: they make m and ℓ_g meaningful
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 12.29, p.73 (PDF p.77)

import Mathlib
import Definitions.Def_ModFormPIR_CharForms
import Definitions.Def_ModFormPIR_Witness

open scoped MatrixGroups

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 12.29**, p.73. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
`A_m²` is a modular form for `Γ(q)` of weight `d + 2m` with a one-dimensional representation of finite order, and `ord_c(A_m²) ≥ d/4 + 2ℓ_c` at every cusp.

**Formalization Note.** Printed under a witness `β` with (42)–(45), which by Theorem 12.2 does not exist. It is stated here for every `β` with (42)–(44), the conditions its proof uses and which `β = 1` on `{b𝟏}` satisfies. A cusp is `g∗∞`; the bound holds for
every lift `g`, with `ℓ_g` computed from that lift (the paper fixes one `g_c` per class). The clause that `liveLevels` is nonempty is Corollary 12.22: it makes `ℓ_g` meaningful. -/
theorem lemma_12_29 (q d : ℕ) [Fact q.Prime] (hodd : Odd q) (hd : 1 ≤ d) (hqd : q ∣ d)
    (β : (Fin d → ZMod q) → ℂ) (hβ : IsNormalizedWitness β)
    (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (hρ : IsWeil q (muHalf q) ρ) :
    ∃ m : ℕ, IsTaylorOrder β m ∧
      IsModularFormChar q (d + 2 * m) (fun τ => taylorA β m τ ^ 2) ∧
      ∀ g : SL(2, ℤ), (liveLevels ρ β g).Nonempty ∧
        (((d : ℝ) / 4 + 2 * ellG ρ β g : ℝ) : EReal) ≤
          cuspOrd q (d + 2 * m) (fun τ => taylorA β m τ ^ 2) g := by sorry

end ModFormPIR
