-- Prove2me | Theorems.Thm_InverseGalois_riemann_existence_realizable_complex
-- name    : InverseGalois.riemann_existence_realizable_complex
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-15T21:06:54.495849+00:00
-- url     : https://prove2.me/theorems/593951be-7fb4-4c74-927c-572c273c85b0
-- title:
--   Riemann existence: a surjection from $\pi_1$ gives a Galois extension of $\mathbb{C}(t)$
-- statement:
--   Let $S \subset \mathbb{C}$ be a finite set, let $x$ be a point of $\mathbb{C}\setminus S$, let $G$ be a finite group, and suppose there is a surjective group homomorphism
--   $$ \varphi : \pi_1(\mathbb{C}\setminus S,\, x) \longrightarrow G . $$
--   Then $G$ is the Galois group of a Galois extension of the rational function field $\mathbb{C}(t)$.
--
--   This is the function-field form of the **Riemann existence theorem**, and it is the unconditional geometric input to the whole inverse Galois problem. The kernel of $\varphi$ has finite index $|G|$, so covering space theory produces a connected covering $Y \to \mathbb{C}\setminus S$ of degree $|G|$ whose group of deck transformations is $G$. The Riemann existence theorem says that this purely topological covering of a smooth affine complex curve carries a unique structure of smooth affine algebraic curve over $\mathbb{C}$ for which the covering map is algebraic; equivalently, every finite topological covering of $\mathbb{C}\setminus S$ is the analytification of an algebraic one. Passing to function fields, $\mathbb{C}(Y)/\mathbb{C}(t)$ is a finite Galois extension of $\mathbb{C}(t)$ whose Galois group is the deck group $G$.
--
--   What the statement does *not* provide is any control over the field of constants. The extension produced is an extension of $\mathbb{C}(t)$, and descending the constants from $\mathbb{C}$ to $\mathbb{Q}$ — the step that Hilbert's irreducibility theorem performs once the constants are already rational — is exactly what separates this theorem from the inverse Galois problem over $\mathbb{Q}$.
--
--   Degenerate cases are included: for $S = \emptyset$ the plane is simply connected, so the hypothesis forces $G$ to be trivial, and the trivial group is realized by the extension $\mathbb{C}(t)/\mathbb{C}(t)$.
--
--   **Formalization Note.** The punctured plane is presented as the subtype of $\mathbb{C}$ consisting of the points lying outside the finite set $S$, carrying its subspace topology. The hypothesis is a surjection of abstract groups; since $G$ is finite, its kernel automatically has finite index, which is all the argument uses.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026), section 'Partial results'; the Riemann existence theorem as in Forster, Lectures on Riemann Surfaces, section 8 (Theorem 8.9, existence of the algebraic structure on a finite covering), and its use for the inverse Galois problem in Voelklein, Groups as Galois Groups, ch. 2-4, and Serre, Topics in Galois Theory, ch. 1

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem riemann_existence_realizable_complex
    {G : Type*} [Fintype G] [Group G]
    (S : Finset ℂ) (x : ℂ) (hx : x ∉ (S : Set ℂ))
    (φ : FundamentalGroup {z : ℂ // z ∉ (S : Set ℂ)} ⟨x, hx⟩ →* G)
    (hφ : Function.Surjective φ) :
    IsRealizable (RatFunc ℂ) G := by sorry

end InverseGalois
