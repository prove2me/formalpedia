-- Prove2me | Theorems.Thm_MoritaEquiv_MoritaData_exists_extension_of_hom
-- name    : MoritaEquiv.MoritaData.exists_extension_of_hom
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-12T20:41:31.377447+00:00
-- url     : https://prove2.me/theorems/237ef72b-3bf4-4f9b-8570-aa5ef51c6b93
-- title:
--   A reduct embedding extends to a $\Sigma^+$-homomorphism of $T^+$-models
-- statement:
--   Let $T$ be a theory in a many-sorted signature $\Sigma$, and let $D$ be Morita data over $T$. Morita data adds product, coproduct, subset and quotient sorts, plus explicitly defined function and predicate symbols, giving the extended signature $\Sigma^+$ and the extended theory $T^+$ (`D.ext`). Let $\Pi : \mathrm{Mod}(T^+) \to \mathrm{Mod}(T)$ be the reduct functor (`D.proj`).
--
--   **Statement.** Let $N, N'$ be models of $T^+$ and let $f : \Pi N \to \Pi N'$ be an elementary embedding between their $\Sigma$-reducts. Then $f$ extends to a sort-indexed family of maps $g_s : N_s \to N'_s$, one for every sort $s$ of $\Sigma^+$, with two properties:
--
--   1. $g$ agrees with $f$ on the old sorts: $g_{s} = f_s$ for every $s \in \Sigma$.
--   2. $g$ commutes with the interpretation of every function symbol $F$ of $\Sigma^+$ (old symbols, new defined symbols, projections $\pi_1, \pi_2$, injections $\iota_1, \iota_2$, inclusions $i$ and quotient maps $\epsilon$): $$g_s\big(F^N(x_1,\dots,x_m)\big) = F^{N'}\big(g_{d_1}(x_1),\dots,g_{d_m}(x_m)\big).$$
--
--   This is the first half of the "Π is full" argument in Barrett–Halvorson. On a new sort, $g$ is forced: a product element goes to the unique element of $N'$ with the images of its two projections, a coproduct element $\iota_j(a)$ goes to $\iota_j(f(a))$, a subset element goes to the unique element whose inclusion is $f(i(z))$, and $\epsilon(a)$ goes to $\epsilon(f(a))$. That these are well defined, and commute with the defined function symbols, follows because $f$ preserves the defining formulas.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, proof of Proposition 5.3 (with Lemma 4.1); uses Theorem 4.3 / Corollary 4.1 of §4.2

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

theorem MoritaData.exists_extension_of_hom {L : Sig} {T : Theory L} (D : MoritaData L T)
    {N N' : Model D.ext} (f : D.proj.obj N ⟶ D.proj.obj N') :
    ∃ g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s,
      (∀ (s : L.Srt) (x : N.str.carrier (D.incl.onSrt s)),
        g (D.incl.onSrt s) x = ElemEmb.toFun f s x) ∧
      ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
        (x : (j : Fin m) → N.str.carrier (dom j)),
        g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)) := by sorry

end MoritaEquiv
