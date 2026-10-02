-- Prove2me | Theorems.Thm_MooreWeakPartialAction_not_forall_exists_const_isWeightedFolner_restrict_compl
-- name    : MooreWeakPartialAction.not_forall_exists_const_isWeightedFolner_restrict_compl
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T22:59:38.606108+00:00
-- url     : https://prove2.me/theorems/aac1c973-3129-4533-8270-cbf4f34d3b45
-- title:
--   Moore Lemma 3.12 fails for partial actions in the weak reading of Definition 3.1
-- statement:
--   It is not true that for every a partial map $\mathbf Z \times \mathbf Z \to \mathbf Z$, $(x, g) \mapsto x \cdot g$ (the acting group written multiplicatively), with $x \cdot e = x$, with $x \cdot g = y$ if and only if $y \cdot g^{-1} = x$, and with $x \cdot (gh) = (x \cdot g) \cdot h$ required only when $x \cdot g$, $(x \cdot g) \cdot h$ and $x \cdot (gh)$ are all defined, every finite symmetric generating set $\Gamma$ and every marginal $E \subseteq \mathbf Z$ with non-empty complement there is a constant $C$ such that, whenever $\mu$ is a weighted $\varepsilon$-Følner set and $C\varepsilon \le 1$, $\mu \restriction (\mathbf Z \setminus E)$ is a weighted $C\varepsilon$-Følner set with non-empty support (Moore's Lemma 3.12, p. 9).
--
--   Moore's Definition 3.1 (p. 5) asks for "$x \cdot (gh) = (x \cdot g) \cdot h$ for all $g, h \in G$ and all $x \in S$ for which all computations involving $\cdot$ are defined". Read weakly, as above, this does not support the lemma. The Moore mission's definitions (`MooreFoelner.IsPartialAction`) read it as Exel's composition law instead: whenever $x \cdot g$ and $(x \cdot g) \cdot h$ are defined, $x \cdot (gh)$ is defined and equals $(x \cdot g) \cdot h$.
--
--   The counterexample: $n \cdot e = n$ and $n \cdot a^{\pm 1} = n \pm 1$ only, with $a = 1$ and $\Gamma = \{a, a^{-1}\}$, and $\mu = 1_{\{1, \dots, N\}}$, whose Følner sum is $4$, so it is a weighted $\varepsilon$-Følner set whenever $\varepsilon N > 4$. No $n \cdot a^{2k}$ with $k > 0$ is defined, so $a^2$ marginalizes every subset of $\mathbf Z$. There $E = \mathbf Z \setminus \{1\}$ is marginal, and for any $C$, taking $C\varepsilon \le 1$ and $N > 4/\varepsilon$, $\mu \restriction \{1\}$ has Følner sum $4$, which is not less than $C\varepsilon$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7 page numbers), p. 5, Definition 3.1 read weakly, and p. 9, Lemma 3.12

import Definitions.Def_MooreFoelner
import Mathlib

namespace MooreWeakPartialAction

theorem not_forall_exists_const_isWeightedFolner_restrict_compl :
    ¬ ∀ (act : ℤ → Multiplicative ℤ → Option ℤ),
      (∀ x, act x 1 = some x) →
      (∀ (g : Multiplicative ℤ) (x y : ℤ), act x g = some y ↔ act y g⁻¹ = some x) →
      (∀ (g h : Multiplicative ℤ) (x y z w : ℤ),
        act x g = some y → act y h = some z → act x (g * h) = some w → w = z) →
      ∀ (Γ : Finset (Multiplicative ℤ)), (∀ γ ∈ Γ, γ⁻¹ ∈ Γ) →
      Subgroup.closure (Γ : Set (Multiplicative ℤ)) = ⊤ →
      ∀ (E : Set ℤ), MooreFoelner.IsMarginal act E → (Eᶜ).Nonempty →
      ∃ C : ℝ, ∀ (ε : ℝ) (μ : ℤ →₀ ℝ), MooreFoelner.IsWeightedFolner act Γ μ ε → C * ε ≤ 1 →
        MooreFoelner.IsWeightedFolner act Γ (MooreFoelner.restrict μ Eᶜ) (C * ε) ∧ (MooreFoelner.restrict μ Eᶜ).support.Nonempty := by
  sorry

end MooreWeakPartialAction
