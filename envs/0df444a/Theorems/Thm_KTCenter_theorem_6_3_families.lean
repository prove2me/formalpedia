-- Prove2me | Theorems.Thm_KTCenter_theorem_6_3_families
-- name    : KTCenter.theorem_6_3_families
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:53.670232+00:00
-- url     : https://prove2.me/theorems/638e063e-5439-4e6b-a046-2bc3a6a71e1c
-- title:
--   Theorem 6.3, family clauses — the walk families have polynomial size, contain comparison members for every $p^*$, and satisfy (46), (55); construction time carried by Theorem 6.1
-- statement:
--   Fix $K$ and positive rationals $C_0,C_1$ and $0<\xi<1$. There is a constant $c$ such that for every cost instance with these parameters and every order of the large blocks, the joint family of EnumerateLargeSamples and the families $G_B$ of EnumerateSmallSamples satisfy:
--
--   1. the number of members of the joint family plus the numbers of members of all $G_B$ is at most $(nN+1)^c$;
--   2. for every residual assignment $p^*$, the joint family contains a member whose guesses agree with $p^*$ and which satisfies (45), and each $G_B$ contains a member whose guesses agree with $p^*$ and which satisfies (54);
--   3. for every member $g$ of the joint family and every $(x,e)\in\mathcal P_\ell(g)$, $|G^\ell_i(x)-H^g_i(x)|\le A/2$ (46);
--   4. for every small $B$, every $h\in G_B$ and every $x\in\mathcal P_{B,h}$, $|G_{iB}(x)-H_{iB}(x,\hat s^{B,h})|\le\kappa|B|^2/2$ (55).
--
--   The construction-time clause of Theorem 6.3 is not part of this item; it is carried by Theorem 6.1.
--
--   Differences from the source:
--
--   - reading: "of polynomial total size" for fixed K, C₀, C₁, ξ → number of distinct members ≤ (nN + 1)^c with c fixed before the instance; reason: the size is a count of members; nN + 1 is polynomial in the instance size
--   - reading: "Order the candidates of each subset B, identify the H states with 0, …, H − 1" → increasing candidate order and state (x, y) ↦ xm + y; reason: the paper leaves these orders free
--   - reading: "in a fixed subset order" → the block order is a universally quantified parameter; reason: every fixed order is covered
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 6.3, p.60 (PDF p.62), with §§6.2.2–6.2.3, pp.62–64 (PDF pp.64–66)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_FixKeys
import Definitions.Def_KTCenter_LP1
import Definitions.Def_KTCenter_MGGWalk
import Definitions.Def_KTCenter_SampleFamilies

namespace KTCenter

/-- **Theorem 6.3, family clauses**, p.60 (PDF p.62), with §§6.2.2–6.2.3, pp.62–64; construction time
carried by Theorem 6.1.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** "Fixed `K, C₀, C₁, ξ`": they and `c` precede the instance. The families are
functions of the instance and the subset order, and `p*` comes after them. "Polynomial total size" is
the number of distinct members, in `ℕ∞` so that it cannot be silently infinite, bounded by a power of
`nN + 1`. The clauses for `N = 0` and `ℬ_ℓ = ∅` are included. -/
theorem theorem_6_3_families (K : ℕ) (C₀ C₁ ξ : ℚ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) :
    ∃ c : ℕ, ∀ (I : CostInstance K C₀ C₁)
      (ord : Fin (I.bLarge ξ).card ≃ {B // B ∈ I.bLarge ξ}),
      {g : I.LargeMember ξ | CostInstance.IsLargeMember ord g}.encard +
          ∑ B : {B // B ∈ I.bSmall ξ},
            {h : I.SampleGuess B.1 | CostInstance.IsSmallMember ξ h}.encard ≤
        (((I.n * I.N + 1) ^ c : ℕ) : ℕ∞) ∧
      (∀ pstar : I.AssignOn (I.Ures ξ),
        (∃ g : I.LargeMember ξ, CostInstance.IsLargeMember ord g ∧
          (∀ B, (g B).AgreesWith pstar) ∧ CostInstance.Cond45 g pstar) ∧
        ∀ B : {B // B ∈ I.bSmall ξ}, ∃ h : I.SampleGuess B.1, CostInstance.IsSmallMember ξ h ∧
          h.AgreesWith pstar ∧ CostInstance.Cond54 h pstar) ∧
      (∀ (φ : I.AssignOn (I.F ξ)) (g : I.LargeMember ξ), CostInstance.IsLargeMember ord g →
        ∀ (x : I.Vec) (e : Fin I.n → I.Vec), CostInstance.InPell g x e → ∀ i : Fin I.n,
          |CostInstance.GLarge φ i x - CostInstance.HLarge φ g i x| ≤ (I.Aell ξ : ℝ) / 2) ∧
      (∀ (φ : I.AssignOn (I.F ξ)) (B : {B // B ∈ I.bSmall ξ}) (h : I.SampleGuess B.1),
        CostInstance.IsSmallMember ξ h → ∀ x : I.Vec, CostInstance.InPB (ξ := ξ) h x → ∀ i : Fin I.n,
          |I.GB ξ φ i B.1 x - I.HB ξ φ i B.1 x (h.estimate i)| ≤
            (I.kappa ξ : ℝ) * (B.1.card : ℝ) ^ 2 / 2) := by sorry

end KTCenter
