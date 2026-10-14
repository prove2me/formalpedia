-- Prove2me | Theorems.Thm_MoritaEquiv_MoritaData_model_ext_newSorts
-- name    : MoritaEquiv.MoritaData.model_ext_newSorts
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-12T19:53:12.994643+00:00
-- url     : https://prove2.me/theorems/0f38718a-4275-473b-939a-24342151d52b
-- title:
--   New sorts of a Morita extension are realised as products, coproducts, subsets and quotients
-- statement:
--   Let $T^+$ be a Morita extension of the $\Sigma$-theory $T$ (new product, coproduct, subsort and quotient sorts together with their explicit definitions $\delta_\sigma$, plus explicitly defined function and predicate symbols), and let $N$ be any model of $T^+$. Write $N|_\Sigma$ for its reduct to $\Sigma$. Then the canonical maps attached to the new sorts are bijections onto their intended targets:
--
--   1. **Product sort** $\sigma$ with projections $\pi_1 : \sigma \to s_1$, $\pi_2 : \sigma \to s_2$: the map $N_\sigma \to N_{s_1} \times N_{s_2}$, $z \mapsto (\pi_1 z, \pi_2 z)$, is bijective.
--   2. **Coproduct sort** $\sigma$ with injections $\rho_1 : s_1 \to \sigma$, $\rho_2 : s_2 \to \sigma$: the copairing $[\rho_1,\rho_2] : N_{s_1} \sqcup N_{s_2} \to N_\sigma$ is bijective.
--   3. **Subsort** $\sigma \subseteq s$ cut out by $\varphi(x)$ with inclusion $i : \sigma \to s$: $i$ is injective, and an element $a \in N_s$ lies in its image iff $N|_\Sigma \models \varphi(a)$.
--   4. **Quotient sort** $\sigma = s/\varphi$ with projection $\varepsilon : s \to \sigma$: $\varepsilon$ is surjective, and $\varepsilon(a) = \varepsilon(b)$ iff $N|_\Sigma \models \varphi(a,b)$.
--
--   This is the semantic content of the defining axioms $\delta_\sigma$ (Barrett–Halvorson §4.1): every element of a new sort is determined by, and determines, data in the old sorts. It is the basic lemma behind the faithfulness and fullness of the reduct functor $\Pi : \mathrm{Mod}(T^+) \to \mathrm{Mod}(T)$ (Propositions 5.2–5.3).
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (arXiv v1), §4.1 (explicit definitions of new sorts) and §5 (proof of Proposition 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- In every model `N` of a Morita extension `T⁺`, the canonical maps attached to the new sorts are
bijections onto their intended targets: `z ↦ (π₁ z, π₂ z)` for a product sort, `[ρ₁, ρ₂]` for a
coproduct sort, the inclusion `i` onto `{a | φ(a)}` for a subsort, and `ε` with kernel `φ(a, b)`
for a quotient sort. -/
theorem MoritaData.model_ext_newSorts {L : Sig} {T : Theory L} (D : MoritaData L T)
    (N : Model D.ext) :
    (∀ σ : D.Prod, Function.Bijective fun z : N.str.carrier (.prod σ) =>
      (N.str.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim))) ∧
    (∀ σ : D.Coprod, Function.Bijective (Sum.elim
      (fun a : N.str.carrier (.old (D.coprodFst σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a
            finZeroElim))
      (fun b : N.str.carrier (.old (D.coprodSnd σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b
            finZeroElim)))) ∧
    (∀ σ : D.Sub, Function.Injective (fun z : N.str.carrier (.sub σ) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim)) ∧
      ∀ a : N.str.carrier (.old (D.subBase σ)),
        (∃ z : N.str.carrier (.sub σ), N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = a) ↔
        (D.subDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.subBase σ] j)) a finZeroElim)) ∧
    (∀ σ : D.Quot, Function.Surjective (fun a : N.str.carrier (.old (D.quotBase σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
            finZeroElim)) ∧
      ∀ a b : N.str.carrier (.old (D.quotBase σ)),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
              finZeroElim) =
          N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) b
              finZeroElim) ↔
        (D.quotDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j)) a
            (Fin.cons
              (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j.succ)) b
              finZeroElim))) := by sorry

end MoritaEquiv
