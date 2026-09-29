-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.le_ord_residue_and_exists_hasValue_of_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c1742302-7eb8-5bcd-acda-775d45e3dc73
-- title:
--   Branch orders and glued twisted values at a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with decidable equality, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$), integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of level $1$ into level $q$, a place specialization $P$ of these data, and a level-one prolongation pair $R$ for $P$ (a coefficient reduction $\overline{red}$ on the residue field of $A$, an embedding $\iota$ of residue function fields, and two regular prolongations $R_1$, $R_2$ of $A$ to $\overline{F}_{1\cdot q} =$ `modularFunctionFieldBar (1 * q)` with residue field `modularFunctionFieldFullC (ResidueField A) 1`, $R_2$ being the transport of $R_1$ along the Fricke involution). Let $a \in k$ lie in `ssJSet q k`, that is: every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no point annihilated by $q$ other than $0$; assume $a^{q^2} = a$. Let $f, t \in \overline{F}_{1\cdot q}$ lie in both valuation subrings $R_1$`.integers` and $R_2$`.integers`. Assume that for every place $W$ of $\overline{F}_{1\cdot q}$ over $\overline{\mathbb Q}$ which is centred at the node $(a, a^q)$, in the sense that some $x \in A$ with $red\,x = a$ has $W.\mathrm{ord}(j - x) > 0$ and some $y \in A$ with $red\,y = a^q$ has $W.\mathrm{ord}(j_{q} - y) > 0$ (here $j$ is the coefficientwise image of the $q$-expansion `jq` and $j_q$ that of `qExpand ℚ (1 * q) jq`), one has $0 \le W.\mathrm{ord}(f t)$. Let $n_1, n_2 \in \mathbb Z$ and $l_1, l_2 \in k$ be nonzero, and suppose that at the first component $\mathrm{charLGeomPlaceOfPoint}\,k\,a$ of `frobNodePair q a` the function $(\tilde j - a)^{-n_1} \cdot R.\mathrm{residue}_1(t)$ takes the value $l_1$, and at the second component $\mathrm{charLGeomPlaceOfPoint}\,k\,(a^q)$ the function $(\tilde j - a^q)^{-n_2} \cdot R.\mathrm{residue}_2(t)$ takes the value $l_2$, taking a value meaning lying in the valuation subring of the place with residue the image of that element of $k$; here $\tilde j =$ `jqModC k` inside `modularFunctionFieldC k 1`. The conclusion is threefold: if $R.\mathrm{residue}_1(f) \ne 0$ then $-n_1 \le \mathrm{ord}(R.\mathrm{residue}_1(f))$ at the first place; if $R.\mathrm{residue}_2(f) \ne 0$ then $-n_2 \le \mathrm{ord}(R.\mathrm{residue}_2(f))$ at the second place; and there exists $c \in k$ such that $(\tilde j - a)^{n_1} \cdot R.\mathrm{residue}_1(f)$ takes the value $l_2 c$ at the first place while $(\tilde j - a^q)^{n_2} \cdot R.\mathrm{residue}_2(f)$ takes the value $l_1 c$ at the second place.
--
--   This is the local step, at a single supersingular crossing of the two branches of the reduction of $X_0(q)$ in characteristic $q$, which supplies both the bound on the branch orders and the matching (glued) twisted values on the two branches, the auxiliary function $t$ playing the role of a local equation there. It is used by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq) to assemble a split datum from local data at all crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.le_ord_residue_and_exists_hasValue_of_mul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f t : ↥(modularFunctionFieldBar (1 * q)))
    (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → 0 ≤ W.ord (f * t))
    (n₁ n₂ : ℤ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-n₁)
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-n₂)
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    (R.residue₁ ⟨f, hf₁⟩ ≠ 0 → -n₁ ≤ (frobNodePair q a).1.ord (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) ∧
    (R.residue₂ ⟨f, hf₂⟩ ≠ 0 → -n₂ ≤ (frobNodePair q a).2.ord (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) ∧
    ∃ c : k,
      (frobNodePair q a).1.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ n₁
          * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k 1))) (l₂ * c) ∧
      (frobNodePair q a).2.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ n₂
          * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k 1))) (l₁ * c) := by sorry
