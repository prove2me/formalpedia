-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/fd9c860f-29c6-56e4-8aa9-a55d77c0d487
-- title:
--   Explicit split datum at one supersingular node, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (X_1^{q}-X_2)(X_1-X_2^{q}) \bmod q$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy embeddings of the geometric modular function field of level $1$ into that of level $1\cdot q$ over $\overline{\mathbb{Q}}$, a place specialization $P$ for these data, and a level-one prolongation pair $R = (R_1,R_2)$ for $P$. Assume $R$ is a model (the two divisor laws and the two cusp laws of `IsModel`), that $S_0$ is a finite subset of $k$ whose members are exactly the elements of `ssJSet q k`, and that $R$ satisfies `RegularityLaw S₀`. Fix $a \in$ `ssJSet q k` with $a^{q^{2}} = a$, and write $\nu_1 =$ `(frobNodePair q a).1`, $\nu_2 =$ `(frobNodePair q a).2` for the places of the level-one geometric function field over $k$ at $\tilde\jmath = a$ and $\tilde\jmath = a^{q}$. Let $E$ be a divisor on the base-changed full modular function field of level $1\cdot q$ with $E(W) \ge 0$ for all $W$, every point $W$ of whose support is strict of the first kind (`IsStrictTypeOne`), strict of the second kind (`IsStrictTypeTwo`), or centred at the node $(a,a^{q})$, meaning that $\mathrm{ord}_W(j - x) > 0$ for some $x \in A$ with $\mathrm{red}\,x = a$ and $\mathrm{ord}_W(j_q - y) > 0$ for some $y \in A$ with $\mathrm{red}\,y = a^{q}$. Let $t$ be an element of the function field lying in the valuation rings of both $R_1$ and $R_2$ with $\mathrm{ord}_W t = E(W)$ for every place $W$ centred at $(a,a^{q})$ in this sense. Let $n_1, n_2 \in \mathbb{N}$ and $l_1, l_2 \in k^{\times}$ satisfy $n_1 + n_2 = (\mathrm{redFst}_* E)(\nu_1)$, and suppose $(\tilde\jmath - a)^{-n_1}\,\mathrm{res}_1(t)$ lies in the valuation ring of $\nu_1$ with residue $l_1$, and $(\tilde\jmath - a^{q})^{-n_2}\,\mathrm{res}_2(t)$ lies in the valuation ring of $\nu_2$ with residue $l_2$. Then `R.SplitDatum S₀ E` holds for the divisors $D_1 = \mathrm{redFst}_*(\mathrm{fstPart}\,E) + n_1\,[\nu_1]$ and $D_2 = \mathrm{redSnd}_*(\mathrm{sndPart}\,E) + n_2\,[\nu_2]$ and the gluing parameter equal to $1$ everywhere except at $a$, where it is $l_2 l_1^{-1}$: that is, at Frobenius-square-fixed places other than the reduction of the cusp $\infty$ the values of $D_1$ and of $D_2$ at the Frobenius image are squeezed between the pushforwards of the negative and positive parts of $E$ and satisfy the tie $D_1(v) + D_2(\varphi v) = (\mathrm{redFst}_* E)(v)$; $\deg D_1 + \deg D_2 = \deg E$; the parameter is non-zero on $S_0$; at places not fixed by $\varphi^{2}$ the divisors agree with the pushforwards of the strict parts of $E$; the values at the reductions of the two cusps are the pushforwards of the $\infty$-side and $0$-side parts of $E$; and for every $f$ in the Riemann–Roch space of $E$ integral for both prolongations, the two residues lie in the Riemann–Roch spaces of $D_1$ and $D_2$ and, for each $b \in S_0$ with $b^{q^{2}} = b$, the residues twisted by the appropriate powers of $\tilde\jmath - b$ and $\tilde\jmath - b^{q}$ take a common value at the two branches over $b$.
--
--   This is the split law for a level-one prolongation pair in the case where all non-strict mass of an effective divisor $E$ is concentrated in the single supersingular tube over $a$ and is cut out there by a function $t$ integral for both prolongations: the two reduced divisors and the gluing parameter are written down explicitly rather than produced existentially, and no inertia-stability of $E$ is required. It feeds the construction of good representatives of divisor classes supported at supersingular points, being cited by `exists_goodRep_admissible_smul_single_sub_self_of_eq_zero_or_eq` and `exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hR : R.IsModel) (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : ∀ W, 0 ≤ E W)
    (hEsupp : ∀ W ∈ E.support, P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W ∨
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (t : ↥(modularFunctionFieldBar (1 * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord t = E W)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.redFst E (frobNodePair q a).1)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-(n₁ : ℤ))
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    R.SplitDatum S₀ E
      (Finsupp.mapDomain P.redFst (P.fstPart E) + Finsupp.single (frobNodePair q a).1 (n₁ : ℤ))
      (Finsupp.mapDomain P.redSnd (P.sndPart E) + Finsupp.single (frobNodePair q a).2 (n₂ : ℤ))
      (Function.update (fun _ => (1 : k)) a (l₂ * l₁⁻¹)) := by sorry
