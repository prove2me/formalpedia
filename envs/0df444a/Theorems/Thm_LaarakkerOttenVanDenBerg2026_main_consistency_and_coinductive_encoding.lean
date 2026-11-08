-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_main_consistency_and_coinductive_encoding
-- name    : LaarakkerOttenVanDenBerg2026.main_consistency_and_coinductive_encoding
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T16:11:04.74635+00:00
-- url     : https://prove2.me/theorems/b98f610d-391a-4120-818f-70c8d087acb8
-- title:
--   Main Theorem: Realisability Model Soundness, Concrete Model Instantiation, Consistency, and Construction of (Co)inductive Types via Large Sizes
-- statement:
--   **Main Theorem of Laarakker, Otten & van den Berg (FSCD 2026, Sections 2–4 & Appendices A–C)**:
--   Over any computable PCA $P : \mathsf{NatPCA}$ (such as Kleene's first algebra $\mathcal{K}_1$):
--   1. **Realisability Model Soundness, Consistency, and Parametricity over $\nabla\omega_1$ (Section 4 & Appendix C)**: In the Category with Families of assemblies over $P$ with semantic size type $\mathsf{semSize}\,P\,\Gamma = \nabla\omega_1$, $\mathsf{botPER}$ has an empty quotient ($\neg\mathrm{Nonempty}(\mathsf{botPER}.\mathrm{Quotient})$), $P$ admits a PCA fixpoint combinator (`IsPCAFixpoint`), the existential size quantifier $\mathsf{semEx}\,P\,\Gamma\,(\lambda \_.\,R)\,\gamma$ on any size-independent $R : \mathsf{PER}$ relates $k_1, k_2 \in \mathbb{N}$ if and only if $R$ relates $(\mathrm{unpair}\,k_1)_2$ and $(\mathrm{unpair}\,k_2)_2$ (Proposition 3a in the model), the universal size quantifier $\mathsf{semAll}\,P\,\Gamma\,C\,\gamma$ relates $d, e \in \mathbb{N}$ if and only if $d$ and $e$ uniformly track $C\langle\gamma, s\rangle$ across all countable ordinals $s \in \omega_1$ and all realisers $m, n \in \mathbb{N}$, every tracked assembly morphism $\nabla\omega_1 \to \iota(R)$ into a modest type is constant across all sizes (Proposition 3b in the model), $\omega_1$ is well-founded with bottom $0$ and strict successor $s < s + 1$, and every family of countable ordinals indexed by a small PER quotient $R.\mathrm{Quotient}$ is strictly bounded below some $\alpha \in \omega_1$ (Section 4.3, p. 15).
--   2. **Concrete Model Instantiation and Consistency of `ParametricSizeTheory.{1, 0}` (Section 4 & Appendix C)**: There exists a concrete model $M : \mathsf{ParametricSizeTheory}.\{1, 0\}$ extending `perSizeCoreTheory` ($M.\mathrm{toSizeCoreTheory} = \mathrm{perSizeCoreTheory}$, so $M.U = \mathrm{ULift}.\{1\}\,\mathsf{PER}$, $M.\mathrm{El}\,R = R.\mathrm{down}.\mathrm{Quotient}$, $M.\mathsf{Size} = \Omega_1$, $M.\mathsf{zero} = 0_{\Omega_1}$, $M.\mathsf{succ} = \mathrm{omega1Succ}$, and $M.\bot_U = \mathrm{ULift.up}\,\mathsf{botPER}$) such that $\neg\mathrm{Nonempty}(M.\mathrm{El}\,M.\bot_U)$ and every polynomial endofunctor $P_{A, B}$ in $M$ admits an initial algebra ($W$-type) and a terminal coalgebra ($M$-type) with tracked half-adjoint equivalence structure maps.
--   3. **General Construction of Inductive $W$-Types and Coinductive $M$-Types via Large Sizes (Sections 2–3, Theorems 11 & 23)**: In any $M : \mathsf{ParametricSizeTheory}.\{u, v\}$, every polynomial endofunctor $P_{A, B}$ (both finitely and infinitely branching) weakly commutes with $\exists$ and $\forall$ and therefore admits both an initial algebra ($W$-type) $\mu P_{A, B} := \exists i.\,(\mu^\Diamond P_{A, B})\,i$ and a terminal coalgebra ($M$-type) $\nu P_{A, B} := \forall i.\,(\nu^\Box P_{A, B})\,i$ with tracked half-adjoint equivalence structure maps.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Sections 2–4 & Appendices A–C (pp. 1–35)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_Model

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem main_consistency_and_coinductive_encoding
    (P : NatPCA) :
    (¬ Nonempty botPER.Quotient ∧
      (∃ (fixComb : ℕ), IsPCAFixpoint P.toPCA fixComb) ∧
      (∀ (Γ : SemCtx.{1} P.toPCA) (γ : Γ.Carrier) (R : PER) (k₁ k₂ : ℕ),
        (semEx P.toPCA Γ (fun _ => R) γ).rel k₁ k₂ ↔
          R.rel (Nat.unpair k₁).2 (Nat.unpair k₂).2) ∧
      (∀ (Γ : SemCtx.{1} P.toPCA) (γ : Γ.Carrier)
        (C : (ctxExt P.toPCA Γ (semSize P.toPCA Γ)).Carrier → PER) (d e : ℕ),
        (semAll P.toPCA Γ C γ).rel d e ↔
          ∀ (s : Omega1) (m n : ℕ),
            ∃ (dm en : ℕ),
              P.app d m = some dm ∧
              P.app e n = some en ∧
              (C ⟨γ, s⟩).rel dm en) ∧
      (∀ (R : PER)
        (g : AsmHom P.toPCA (nabla P.toPCA Omega1) (iotaModLift.{1} P.toPCA R).toAsm)
        (s₁ s₂ : Omega1),
        g.toFun s₁ = g.toFun s₂) ∧
      (WellFounded (fun (s₁ s₂ : Omega1) => s₁ < s₂) ∧
        ∀ (s : Omega1), omega1Zero ≤ s ∧ s < omega1Succ s) ∧
      (∀ (R : PER) (f : R.Quotient → Omega1),
        ∃ (α : Omega1), ∀ (c : R.Quotient), omega1Succ (f c) ≤ α)) ∧
    (∃ (M : ParametricSizeTheory.{1, 0}),
      M.toSizeCoreTheory = perSizeCoreTheory ∧
      ¬ Nonempty (M.El M.botU) ∧
      ∀ (A : M.U) (B : M.El A → M.U),
        (∃ (hEx : WeaklyCommutesEx M.toSizeCoreTheory
            (polyEndofunctor M.toSizeCoreTheory A B)),
          Nonempty (IsInitialFAlg (muAlg M.toSizeCoreTheory hEx)) ∧
          Nonempty (IsTrackedHAEquiv M.toSizeCoreTheory (muAlg M.toSizeCoreTheory hEx).str)) ∧
        (∃ (hAll : WeaklyCommutesAll M.toSizeCoreTheory
            (polyEndofunctor M.toSizeCoreTheory A B)),
          Nonempty (IsTerminalFCoalg (nuCoalg M.toSizeCoreTheory hAll)) ∧
          Nonempty (IsTrackedHAEquiv M.toSizeCoreTheory (nuCoalg M.toSizeCoreTheory hAll).str))) ∧
    ∀ (M : ParametricSizeTheory.{u, v}) (A : M.U) (B : M.El A → M.U),
      (∃ (hEx : WeaklyCommutesEx M.toSizeCoreTheory
          (polyEndofunctor M.toSizeCoreTheory A B)),
        Nonempty (IsInitialFAlg (muAlg M.toSizeCoreTheory hEx)) ∧
        Nonempty (IsTrackedHAEquiv M.toSizeCoreTheory (muAlg M.toSizeCoreTheory hEx).str)) ∧
      (∃ (hAll : WeaklyCommutesAll M.toSizeCoreTheory
          (polyEndofunctor M.toSizeCoreTheory A B)),
        Nonempty (IsTerminalFCoalg (nuCoalg M.toSizeCoreTheory hAll)) ∧
        Nonempty (IsTrackedHAEquiv M.toSizeCoreTheory (nuCoalg M.toSizeCoreTheory hAll).str)) := by
  sorry

end LaarakkerOttenVanDenBerg2026
