-- Prove2me | Theorems.Thm_MoritaEquiv_translation
-- name    : MoritaEquiv.translation
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T12:59:41.272765+00:00
-- url     : https://prove2.me/theorems/936ea020-8ce9-41e1-a85d-a8994f3b708d
-- title:
--   Translation of Σ⁺-formulas with old-sorted free variables
-- statement:
--   Throughout: many-sorted first-order logic with nonempty sorts; $\mathrm{Mod}(T)$ has the models of $T$ as objects and elementary embeddings as arrows; $D$ is a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts and explicitly defined symbols, with admissibility in every model of $T$), $T^+$ the extended theory and $\Pi:\mathrm{Mod}(T^+)\to\mathrm{Mod}(T)$ the reduct functor. Every $\Sigma^+$-formula $\varphi$ whose context consists of old sorts is $T^+$-equivalent to (the image of) some $\Sigma$-formula $\psi$ in the same context.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §4.2, Theorem 4.3 and Corollary 4.1 (proof in the appendix)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 4.3 / Corollary 4.1 (case of free variables of old sorts):
if `T⁺` is a Morita extension of `T`, every `Σ⁺`-formula `φ` whose free variables all have sorts
in `Σ` is `T⁺`-equivalent to (the image of) a `Σ`-formula `ψ` in the same variables. -/
theorem translation {L : Sig} {T : Theory L} (D : MoritaData L T) {n : ℕ} (Γ : Fin n → L.Srt)
    (φ : Formula D.sig (D.incl.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (N : Model D.ext) (v : (i : Fin n) → N.str.carrier (D.incl.onSrt (Γ i))),
      φ.Realize N.str v ↔ (ψ.onFormula D.incl).Realize N.str v := by sorry

end MoritaEquiv
