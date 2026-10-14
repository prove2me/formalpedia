-- Prove2me | Theorems.Thm_MoritaEquiv_MoritaData_isModel_ext_iff
-- name    : MoritaEquiv.MoritaData.isModel_ext_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-12T23:48:31.595076+00:00
-- url     : https://prove2.me/theorems/b5e7eef3-50fa-41be-8eea-d58d08ad4a20
-- title:
--   Semantic characterization of models of a Morita extension
-- statement:
--   Let $T$ be a theory in a many-sorted signature $\Sigma$, and let $D$ be Morita data over $T$. The data $D$ specifies new product, coproduct, subset and quotient sorts with their symbols $\pi_1,\pi_2$, $\iota_1,\iota_2$, $i$, $\epsilon$, together with explicitly defined function and relation symbols. This gives the extended signature $\Sigma^+$ and the Morita extension $T^+ = T \cup \{\text{defining axioms}\}$ (`D.ext`).
--
--   **Statement.** A $\Sigma^+$-structure $M$ is a model of $T^+$ if and only if all of the following hold:
--
--   1. the $\Sigma$-reduct $M|_\Sigma$ is a model of $T$;
--   2. for each product sort $\sigma = s_1\times s_2$: for all $a\in M_{s_1}$, $b \in M_{s_2}$ there is a unique $z\in M_\sigma$ with $\pi_1(z)=a$ and $\pi_2(z)=b$;
--   3. for each coproduct sort $\sigma = s_1 + s_2$: every $c \in M_\sigma$ is $\iota_1(a)$ for a unique $a$ or $\iota_2(b)$ for a unique $b$, and $\iota_1(a) \neq \iota_2(b)$ for all $a, b$;
--   4. for each subset sort $\sigma = \{x : s \mid \varphi(x)\}$: $M|_\Sigma \models \varphi[a] \iff \exists z\in M_\sigma,\ i(z)=a$, for all $a \in M_s$, and $i$ is injective;
--   5. for each quotient sort $\sigma = s/\varphi$: $\epsilon(a)=\epsilon(b) \iff M|_\Sigma\models\varphi[a,b]$, and $\epsilon$ is surjective;
--   6. each new function symbol $f$ with definition $\psi(y,\bar x)$ satisfies $f^M(\bar x)=y \iff M|_\Sigma\models\psi[y,\bar x]$;
--   7. each new relation symbol $r$ with definition $\psi(\bar x)$ satisfies $r^M(\bar x)\iff M|_\Sigma\models\psi[\bar x]$.
--
--   This is the semantic reading of the definition of a Morita extension. It turns "$M \models T^+$" into concrete conditions on the interpretations of the new sorts and symbols, which makes it the basic tool for checking that a proposed structure is a model of a Morita extension, for example in the worked examples of Barrett–Halvorson.
--
--   **Formalization Note** Conditions 2–7 are stated literally as the realization of each defining axiom: unary symbol applications appear as `funMap` on a one-element tuple, and the variable assignments are indexed by `Fin n`.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §4: definition of a Morita extension and the defining axioms for product, coproduct, subset and quotient sorts and for explicitly defined symbols

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Semantic characterization of the models of a Morita extension. A `D.sig`-structure `M` is a
model of `T⁺ = D.ext` iff its reduct to `L` is a model of `T` and `M` satisfies, read off literally,
each defining axiom: `π₁, π₂` make each product sort a product; `ι₁, ι₂` are jointly surjective,
individually injective (uniqueness of the preimage) with disjoint images on each coproduct sort; each
inclusion `i` is injective with image `{a | φ(a)}`; each quotient map `ε` is surjective with kernel
`φ(a, b)`; and each new function or relation symbol is interpreted by its defining formula. -/
theorem MoritaData.isModel_ext_iff {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Str D.sig) :
    M.IsModel D.ext ↔
    (M.reduct D.incl).IsModel T ∧
    (∀ σ : D.Prod,
    ∀ v : (i : Fin 2) → M.carrier
        ((![MoritaData.ExtSrt.old (D.prodFst σ), MoritaData.ExtSrt.old (D.prodSnd σ)] : Fin 2 → D.sig.Srt) i),
      ∃ z : M.carrier (.prod σ), (M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 0 ∧
        M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 1) ∧
        ∀ z' : M.carrier (.prod σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 0 ∧
          M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 1 → z' = z) ∧
    (∀ σ : D.Coprod,
    ∀ v : (i : Fin 1) → M.carrier ((![MoritaData.ExtSrt.coprod σ] : Fin 1 → D.sig.Srt) i),
      ((∃ a : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = v 0 ∧
          ∀ a' : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a' finZeroElim) = v 0 → a' = a) ∨
        (∃ b : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim) = v 0 ∧
          ∀ b' : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b' finZeroElim) = v 0 → b' = b)) ∧
      ∀ (a : M.carrier (.old (D.coprodFst σ))) (b : M.carrier (.old (D.coprodSnd σ))),
        ¬ M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim)) ∧
    (∀ σ : D.Sub,
    ∀ v : (i : Fin 1) → M.carrier ((D.incl.onSrt ∘ ![D.subBase σ] : Fin 1 → D.sig.Srt) i),
      ((D.subDef σ).Realize (M.reduct D.incl) v ↔
          ∃ z : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = v 0) ∧
        ∀ z₁ z₂ : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₂ finZeroElim) =
          M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₁ finZeroElim) → z₂ = z₁) ∧
    (∀ σ : D.Quot,
    ∀ v : (i : Fin 2) → M.carrier
        ((D.incl.onSrt ∘ ![D.quotBase σ, D.quotBase σ] : Fin 2 → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 0) finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 1) finZeroElim) ↔
          (D.quotDef σ).Realize (M.reduct D.incl) v) ∧
        ∀ z : M.carrier (.quot σ), ∃ x : M.carrier (.old (D.quotBase σ)),
          M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) x finZeroElim) = z) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s),
    ∀ v : (i : Fin (m + 1)) → M.carrier ((D.incl.onSrt ∘ Ctx.cons s dom : Fin (m + 1) → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.new f) (fun j => v j.succ) = v 0 ↔
        (D.funcDef f).Realize (M.reduct D.incl) v)) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom),
    ∀ v : (i : Fin m) → M.carrier ((D.incl.onSrt ∘ dom : Fin m → D.sig.Srt) i),
      (M.relMap (L := D.sig) (MoritaData.ExtRel.new r) (fun j => v j) ↔
        (D.relDef r).Realize (M.reduct D.incl) v)) := by sorry

end MoritaEquiv
