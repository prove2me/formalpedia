-- Prove2me | Theorems.Thm_LocalNewvector_AdelicSpan_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
-- name    : LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e0624a9f-5786-5d9c-96df-35f8c345e2ce
-- title:
--   Non-zero K₁(qᵃ)-fixed vector inside the local span at q
-- statement:
--   Let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ (the adeles of $\mathbb{Q}$ formed with $\mathcal{O}_{\mathbb{Q}}$), let $N_0$ be a non-zero natural number, and assume that $\varphi$ is right invariant under the level-one congruence subgroup of the ideal $(N_0)$ of $\mathcal{O}_{\mathbb{Q}}$: for every $g$ in the subgroup of $\mathrm{GL}_2$ of the finite adeles whose matrix and whose inverse matrix both satisfy the level-one conditions at $(N_0)$ (level-zero conditions together with the lower-right entry congruent to $1$ in the corresponding ideal ball), and every $x$, one has $\varphi(x\cdot \iota(g)) = \varphi(x)$, where $\iota$ is the embedding of $\mathrm{GL}_2$ of the finite adeles into $\mathrm{GL}_2$ of the adeles that is the identity at the infinite places. Let $q$ be a prime and $a$ a natural number. Write $V$ for the adelic span of $\varphi$, the $\mathbb{C}$-span of all translates $g\cdot\varphi$, $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, regarded as a type, and $K_1(q^a)$ for the subgroup of $\mathrm{GL}_2(\mathbb{Q}_q)$ consisting of the images of matrices $y \in \mathrm{GL}_2(\mathbb{Z}_q)$ with $y_{10} \in (q^a)$ and $y_{11} - 1 \in (q^a)$. Assuming the submodule of $V$ fixed by $K_1(q^a)$ (acting through the place $q$) is non-zero, the conclusion produces $y \in V$ that lies in the $\mathbb{C}$-span of the local translates $\{x \cdot \varphi : x \in \mathrm{GL}_2(\mathbb{Q}_q)\}$ of the distinguished vector $\varphi$ of $V$, is non-zero, and is fixed by every element of $K_1(q^a)$.
--
--   This is the descent step in the local theory of newvectors in the sense of Casselman: a $K_1(q^a)$-fixed vector anywhere in the full adelic span of $\varphi$ can be replaced by one inside the span of the translates of $\varphi$ by $\mathrm{GL}_2(\mathbb{Q}_q)$ alone, so that the conductor exponent at $q$ may be computed purely locally. It is used in the identification of the newvector conductor of the adelic span of the weight-one lift of a primitive form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_AdelicSpan_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq.lean

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm DihedralWeightOne IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
    (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N₀),
      ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (q : ℕ) [Fact q.Prime] (a : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan φ) := by sorry
