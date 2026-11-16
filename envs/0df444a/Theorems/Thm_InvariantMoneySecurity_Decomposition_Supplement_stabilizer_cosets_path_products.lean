-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_Supplement_stabilizer_cosets_path_products
-- name    : InvariantMoneySecurity.Decomposition.Supplement.stabilizer_cosets_path_products
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:33:42.454374+00:00
-- url     : https://prove2.me/theorems/e5606fd3-ddaa-4957-b255-916ac2eaa459
-- title:
--   Lemma 4.6 — stabilizer cosets and path products
-- statement:
--   Let $x$ be an element of the ground set of an invariant money scheme, $C:=C_{k(x)}$ its orbit, and $W$ a finite group acting on $C$ such that $\varphi_x(w):=w\cdot x$ maps $W$ onto $C$. For $y\in C$ write $W_{x\to y}:=\{w\in W:\ w\cdot x=y\}$ for the fibre over $y$, and $\mathrm{Stab}(x):=W_{x\to x}$.
--
--   1. $\mathrm{Stab}(x)$ is a subgroup of $W$; for every $y\in C$ and every $w\in W_{x\to y}$ the fibre is the left coset
--   $$W_{x\to y}=w\,\mathrm{Stab}(x);$$
--   every fibre has $|\mathrm{Stab}(x)|$ elements, and $|W|=|C|\,|\mathrm{Stab}(x)|$.
--   2. Suppose the action goes through the moves: there are $g_s\in W$, one for each move $s$, with $\varphi_x(g_s w)=s(\varphi_x(w))$ for all $w\in W$. If $s_\ell\cdots s_1$ is a path from $x$ to $y$, then $g_{s_\ell}\cdots g_{s_1}\in W_{x\to y}$. Consequently, given for every $y\in C$ some path from $x$ to $y$, the map sending $y$ to the product along its path is a section, i.e. it lands in the fibre over $y$ for every $y$.
--
--   Part 1 gives the fibre sizes and the coset form of the fibres used to relabel fibres in the proof of Theorem 4.8; part 2 turns a path-finder's word into a group element over the target.
--
--   **Formalization Note** The action is a Mathlib `MulAction` of $W$ on the subtype of the orbit, and $x_0$ is $x$ viewed as an element of $C$. A word is a list of move indices in the order of application, and the product along it is $g_{s_\ell}\cdots g_{s_1}$.
--
--   Differences from the source:
--   - generalization: a coset parameterization $(W,\varphi_x)$ (labels are bit strings; multiplication, inversion, the action and the preparation of $|W\rangle$ are polynomial-time) → any finite group acting on $C$ with $\varphi_x(w)=w\cdot x$ onto $C$, with no computability; reason: the lemma uses only the algebra, and every coset parameterization is such an action.
--   - encoding: "Stab(x) is a subgroup" → there is a subgroup whose elements are exactly the $w$ with $w\cdot x=x$, and the coset is taken with Mathlib's stabilizer subgroup; reason: same set, same group.
--   - reading: "So a path-finder that succeeds on every target supplies a section" → for every assignment of a path from $x$ to $y$ to each $y\in C$, the product along the assigned path lies in the fibre over $y$; reason: this is the content of the sentence (the section maps $y$ to the product along the returned path), stated without a computational model of the path-finder.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 18, Lemma 4.6 (Definition 4.3 on p. 17)

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_Words
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition
open scoped Pointwise

/-- Lemma 4.6, p. 18, both parts, for an arbitrary finite group `W` acting on the orbit
`C = C_{k(x)}` with `φ_x(w) = w • x₀` onto `C` (`x₀` is `x` viewed in `C`). Polynomial-time
computability of the coset parameterization is not needed and is not assumed. -/
theorem stabilizer_cosets_path_products {n : ℕ} (D : FiniteScheme n) (x : D.Object)
    (W : Type) [Group W] [Fintype W] [MulAction W {y // y ∈ D.orbit x}]
    (x₀ : {y // y ∈ D.orbit x}) (hx₀ : x₀.val = x.val)
    (honto : ∀ y : {y // y ∈ D.orbit x}, ∃ w : W, w • x₀ = y) :
    ((∃ S : Subgroup W, ∀ w : W, w ∈ S ↔ w • x₀ = x₀) ∧
      (∀ (y : {y // y ∈ D.orbit x}) (w : W), w • x₀ = y →
        {w' : W | w' • x₀ = y} = w • (MulAction.stabilizer W x₀ : Set W)) ∧
      (∀ y : {y // y ∈ D.orbit x},
        Nat.card {w : W // w • x₀ = y} = Nat.card (MulAction.stabilizer W x₀)) ∧
      Fintype.card W = (D.orbit x).card * Nat.card (MulAction.stabilizer W x₀)) ∧
    ∀ g : Fin D.moveCount → W,
      (∀ s (w : W), ((g s * w) • x₀).val = moveBits D s (w • x₀).val) →
      (∀ (l : List (Fin D.moveCount)) (y : {y // y ∈ D.orbit x}),
          (applyWord D l x).val = y.val → wordProduct g l • x₀ = y) ∧
      (∀ path : {y // y ∈ D.orbit x} → List (Fin D.moveCount),
          (∀ y, (applyWord D (path y) x).val = y.val) →
          ∀ y, wordProduct g (path y) • x₀ = y) := by sorry

end InvariantMoneySecurity.Decomposition.Supplement
