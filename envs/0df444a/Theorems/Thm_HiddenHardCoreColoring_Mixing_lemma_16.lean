-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_16
-- name    : HiddenHardCoreColoring.Mixing.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:51.172479+00:00
-- url     : https://prove2.me/theorems/07370d03-e9f8-4c9b-8424-060d445cc82d
-- title:
--   Lemma 16 — given the background η, the color class of a lift is hard-core with activities λ(η)
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). Fix a color $c$ and let $(\eta,I)\sim\hat\mu_c$ be a lift of a uniform coloring. Conditioned on $\eta$, the independent set $I$ has the hard-core distribution $\nu_\eta$ with activities $\lambda_v(\eta)=1/(|A_v(\eta)|-1)$:
--   $$\hat\mu_c(\eta,I)=\rho_c(\eta)\,\nu_\eta(I)\qquad\text{for every }\eta\in\Omega^{-c},\ I\in\mathcal I .$$
--
--   This identifies the hard-core model hidden in a color class.
--
--   Differences from the source:
--   - encoding: conditioned on η, I has distribution ν_η → µ̂_c(η, I) = ρ_c(η) ν_η(I) for every pair; reason: the factorization of the joint law through its η-marginal is the definition of the conditional law; it also covers η with ρ_c(η) = 0
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 16, p.19

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 16** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.19). Let `(η, I) ∼ µ̂_c`. Conditioned on `η`, the independent set `I` has
distribution `ν_η`: `µ̂_c(η, I) = ρ_c(η) ν_η(I)` for every pair. -/
theorem lemma_16 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (c : Fin q) (η : Bg G q c) (I : IndSet G) :
    muHat G c (η, I) = rho G c η * nuEta G c η I := by sorry

end HiddenHardCoreColoring.Mixing
