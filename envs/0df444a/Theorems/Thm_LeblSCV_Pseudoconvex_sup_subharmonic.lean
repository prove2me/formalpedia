-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_sup_subharmonic
-- name    : LeblSCV.Pseudoconvex.sup_subharmonic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:13:27.402316+00:00
-- url     : https://prove2.me/theorems/0ed6bfcc-6703-40ab-b2a3-3d7f52c2dad7
-- title:
--   Proposition 2.4.7 — supremum of a family of subharmonic functions
-- statement:
--   Let $U \subset \mathbb{C}$ be open and let $\{f_\alpha\}$ be a family of subharmonic functions $f_\alpha : U \to \mathbb{R} \cup \{-\infty\}$. Put
--   $$\varphi(z) = \sup_\alpha f_\alpha(z).$$
--   If the family is finite, then $\varphi$ is subharmonic. If $\varphi(z) \neq \infty$ for all $z \in U$ and $\varphi$ is upper-semicontinuous, then $\varphi$ is subharmonic.
--
--   Taking maxima is the basic way to glue plurisubharmonic functions, for example $\max\{-\log\rho, \|z\|^2\}$ in the proof of Theorem 2.5.6.
--
--   **Formalization Note.** The family is indexed by an arbitrary type $\iota$, and the supremum is taken in `EReal`. The book states the second part for infinite families; the formal statement asserts it for every family, which adds nothing because finite families are already covered by the first part. An empty family gives the constant $-\infty$, which is subharmonic under Definition 2.4.1.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 83, Proposition 2.4.7

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsSubharmonicOn

namespace LeblSCV.Pseudoconvex

/-- Proposition 2.4.7 (Lebl, p. 83). Let `U ⊂ ℂ` be open and `f_α : U → ℝ ∪ {−∞}` a family of
subharmonic functions, `φ(z) = sup_α f_α(z)` (supremum in `EReal`). If the family is finite,
`φ` is subharmonic. If `φ(z) ≠ ∞` for all `z ∈ U` and `φ` is upper-semicontinuous, `φ` is
subharmonic (the book states this second part for infinite families; for finite families it is
implied by the first). -/
theorem sup_subharmonic {ι : Type*} (U : Set ℂ) (hU : IsOpen U) (f : ι → ℂ → EReal)
    (hf : ∀ α, IsSubharmonicOn (f α) U) :
    (Finite ι → IsSubharmonicOn (fun z => ⨆ α, f α z) U) ∧
    ((∀ z ∈ U, (⨆ α, f α z) ≠ ⊤) → UpperSemicontinuousOn (fun z => ⨆ α, f α z) U →
      IsSubharmonicOn (fun z => ⨆ α, f α z) U) := by sorry

end LeblSCV.Pseudoconvex
