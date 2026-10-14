-- Prove2me | Theorems.Thm_MoritaEquiv_MoritaData_elemEmb_of_reduct
-- name    : MoritaEquiv.MoritaData.elemEmb_of_reduct
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-12T20:42:37.209267+00:00
-- url     : https://prove2.me/theorems/67a47e92-9320-4140-ae8d-0709d9d09481
-- title:
--   A $\Sigma^+$-homomorphism elementary on old sorts is elementary
-- statement:
--   Same setting: $T$ is a $\Sigma$-theory, $D$ is Morita data with extension $T^+$ in signature $\Sigma^+$, and $N, N'$ are models of $T^+$.
--
--   **Statement.** Let $g = (g_s)_{s \in \Sigma^+}$ be a sort-indexed family of maps $g_s : N_s \to N'_s$ satisfying:
--
--   * (**homomorphism**) $g$ commutes with the interpretation of every function symbol of $\Sigma^+$, and
--   * (**elementary on old sorts**) the restriction of $g$ to the old sorts is an elementary embedding of $\Sigma$-reducts: for every $\Sigma$-formula $\varphi(\bar x)$ and every assignment $\bar v$ in $N$, $$\Pi N' \models \varphi[g(\bar v)] \iff \Pi N \models \varphi[\bar v].$$
--
--   Then $g$ is an elementary embedding of $\Sigma^+$-structures: for every $\Sigma^+$-formula $\varphi(\bar x)$, in any context of $\Sigma^+$-sorts, and every assignment $\bar v$ in $N$, $$N' \models \varphi[g(\bar v)] \iff N \models \varphi[\bar v].$$
--
--   This is the second half of the "Π is full" argument in Barrett–Halvorson. Each variable of a new sort is represented by variables of old sorts: product elements by their projections, coproduct elements by a preimage under an injection, subset elements by their inclusion, and quotient elements by a representative. This turns $\varphi$ into a $\Sigma^+$-formula in old-sorted variables. By the translation theorem (Barrett–Halvorson, Theorem 4.3 / Corollary 4.1), that formula is $T^+$-equivalent to a $\Sigma$-formula, and elementarity on the reducts applies to the $\Sigma$-formula. The homomorphism property of $g$ carries the representation from $N$ over to $N'$.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, proof of Proposition 5.3 (with Lemma 4.1); uses Theorem 4.3 / Corollary 4.1 of §4.2

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

theorem MoritaData.elemEmb_of_reduct {L : Sig} {T : Theory L} (D : MoritaData L T)
    (N N' : Model D.ext) (g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s)
    (hfun : ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
      (x : (j : Fin m) → N.str.carrier (dom j)),
      g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)))
    (hold : ∀ {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ)
      (v : (i : Fin n) → (N.str.reduct D.incl).carrier (Γ i)),
      φ.Realize (N'.str.reduct D.incl) (fun i => g (D.incl.onSrt (Γ i)) (v i)) ↔
        φ.Realize (N.str.reduct D.incl) v) :
    ∀ {n : ℕ} {Γ : Fin n → D.sig.Srt} (φ : Formula D.sig Γ) (v : (i : Fin n) → N.str.carrier (Γ i)),
      φ.Realize N'.str (fun i => g (Γ i) (v i)) ↔ φ.Realize N.str v := by sorry

end MoritaEquiv
