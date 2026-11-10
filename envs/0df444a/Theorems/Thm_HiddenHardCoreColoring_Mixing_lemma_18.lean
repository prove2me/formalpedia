-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_18
-- name    : HiddenHardCoreColoring.Mixing.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:52.724223+00:00
-- url     : https://prove2.me/theorems/5c815d44-932b-48af-9d94-12d8258adc27
-- title:
--   Lemma 18 — lifting and averaging: (a) E_ρ⟨f↑, H_η f↑⟩ = ⟨f, L_c f⟩; (b) E_ρ⟨F_η, H_η F_η⟩ ≥ M_c(F↓)
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). Fix a color $c$.
--   1. For every $f\in L^2(\mu)$,
--   $$\mathbb E_{\eta\sim\rho_c}\big[\langle f^\uparrow_\eta,H_\eta f^\uparrow_\eta\rangle_{\nu_\eta}\big]=\langle f,L_cf\rangle_\mu .$$
--   2. For every function $F$ on $\Omega^{-c}\times\mathcal I$,
--   $$\mathbb E_{\eta\sim\rho_c}\big[\langle F_\eta,H_\eta F_\eta\rangle_{\nu_\eta}\big]\ge M_c(F^\downarrow).$$
--   Here $f^\uparrow_\eta(I)=f(\pi_c(\eta,I))$, $F_\eta=F(\eta,\cdot)$ and $F^\downarrow(\sigma)$ is the mean of $F$ over a random lift of $\sigma$.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 18, eqs. (25)–(26), p.20

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 18** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.20, eqs. (25)–(26)). (a) For every `f`,
`E_{η∼ρ_c}⟨f↑_η, H_η f↑_η⟩_{ν_η} = ⟨f, L_c f⟩_µ`. (b) For every `F` on pairs,
`E_{η∼ρ_c}⟨F_η, H_η F_η⟩_{ν_η} ≥ M_c(F↓)`. -/
theorem lemma_18 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (c : Fin q) :
    (∀ f : Col G q → ℝ,
      ∑ η : Bg G q c, rho G c η *
          ipEta G c η (fiber G (up G c f) η) (Heta G c η *ᵥ fiber G (up G c f) η) =
        ip G q f (Lc G q c *ᵥ f)) ∧
    (∀ F : Bg G q c × IndSet G → ℝ,
      Mc G q c (down G c F) ≤
        ∑ η : Bg G q c, rho G c η * ipEta G c η (fiber G F η) (Heta G c η *ᵥ fiber G F η)) := by sorry

end HiddenHardCoreColoring.Mixing
