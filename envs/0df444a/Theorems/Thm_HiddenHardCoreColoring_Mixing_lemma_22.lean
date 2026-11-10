-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_22
-- name    : HiddenHardCoreColoring.Mixing.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:47.575711+00:00
-- url     : https://prove2.me/theorems/74c5930d-ff1d-4780-8ae5-8ec92840469a
-- title:
--   Lemma 22 — (a) W_{v,c}(f↑) = V_{v,c}(f); (b) V_c(F↓) ≤ W_c(F)
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). Assume also $q\ge(1+1/e)\Delta$ (the standing assumption of §§7.2–7.5). Fix a color $c$.
--   1. $W_{v,c}(f^\uparrow)=V_{v,c}(f)$ for every $f\in L^2(\mu)$ and every vertex $v$.
--   2. $V_c(F^\downarrow)\le W_c(F)$ for every function $F:\Omega^{-c}\times\mathcal I\to\mathbb R$.
--
--   Here $W_{v,c}(F)=\tfrac12\mathbb E_{\hat\mu_c}[\mathbf 1\{v\in V_{\mathrm{ubl}}(I)\setminus I\}p_v(\eta)E_v^{-c}(F(\eta^{v\leftarrow c'},I)-F(\eta,I))^2]$ and $W_c=\sum_vW_{v,c}$.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 22, p.25; standing assumption q ≥ (1 + 1/e)Δ of §7.2, p.24

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 22** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.25), under the standing assumptions and `q ≥ (1 + 1/e)Δ` of §7.2.
(a) `W_{v,c}(f↑) = V_{v,c}(f)` for every `f` and every vertex `v`. (b) `V_c(F↓) ≤ W_c(F)` for every
function `F` on pairs. -/
theorem lemma_22 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (hq1 : (1 + 1 / Real.exp 1) * (Δ : ℝ) ≤ (q : ℝ)) (c : Fin q) :
    (∀ (f : Col G q → ℝ) (v : V), Wvc G v c (up G c f) = Vvc G q v c f) ∧
      (∀ F : Bg G q c × IndSet G → ℝ, Vc G q c (down G c F) ≤ Wc G c F) := by sorry

end HiddenHardCoreColoring.Mixing
